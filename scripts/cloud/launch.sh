#!/bin/bash
# Launch ONE spot instance for a stage (eu-north-1 only, profile kobon) -- run by the owner.
#   bash scripts/cloud/launch.sh STAGE [--dry-run] [--az eu-north-1b] [--type T] [--maxprice P] [--cap USD]
# Hard stops, all three independent of the Mac:
#   * spot MaxPrice: the hourly price can never exceed it;
#   * user-data arms `shutdown -h +N` at boot, N = floor(cap / maxprice * 60) - 10, and the
#     instance is launched with --instance-initiated-shutdown-behavior terminate, so the
#     power-off TERMINATES it (disk deleted with it): cost <= cap + EBS;
#   * run_stage.sh pulls the power-off forward to 60 min after the stage ends.
# Plus the Mac-side meter: python3 scripts/cloud/cost_meter.py --enforce --loop 600
# --dry-run asks EC2 to validate the request without creating anything.
set -euo pipefail
cd "$(dirname "$0")/../.."
export AWS_PROFILE=kobon AWS_REGION=eu-north-1 AWS_PAGER=""
STAGE="${1:?stage}"; shift
DRY=""; AZ=""; TYPE=""; MAXP=""; CAP=""
while [ $# -gt 0 ]; do
  case "$1" in
    --dry-run) DRY="--dry-run" ;;
    --az) AZ="$2"; shift ;;
    --type) TYPE="$2"; shift ;;
    --maxprice) MAXP="$2"; shift ;;
    --cap) CAP="$2"; shift ;;
    *) echo "unknown option $1"; exit 2 ;;
  esac; shift
done
# defaults per stage (derivation: notes/FEASIBILITY.md section 11)
case "$STAGE" in
  stage1) : "${TYPE:=c8g.48xlarge}" "${MAXP:=1.30}" "${CAP:=5}"  ; DISK=40 ;;
  stage2) : "${TYPE:=c8g.48xlarge}" "${MAXP:=1.30}" "${CAP:=14}" ; DISK=60 ;;
  stage12) : "${TYPE:=c8g.48xlarge}" "${MAXP:=1.30}" "${CAP:=18}" ; DISK=60 ;;
  stage3) : "${TYPE:=m8g.48xlarge}" "${MAXP:=1.40}" "${CAP:=40}" ; DISK=60 ;;
  stage3-*) : "${TYPE:=m8g.24xlarge}" "${MAXP:=0.70}" "${CAP:=25}" ; DISK=40 ;;
  *) echo "unknown stage"; exit 2 ;;
esac
SHUT=$(python3 -c "print(max(30, int($CAP / $MAXP * 60) - 10))")
UD=$(mktemp -t tr-ud)
sed "s/@@SHUTDOWN_MIN@@/$SHUT/" scripts/cloud/user-data.sh > "$UD"
PLACE=(); [ -n "$AZ" ] && PLACE=(--placement "AvailabilityZone=$AZ")
echo "stage=$STAGE type=$TYPE maxprice=$MAXP/h cap=\$$CAP hard-stop=${SHUT}min disk=${DISK}GB az=${AZ:-auto} $DRY"
OUT=$(aws ec2 run-instances $DRY \
  --image-id ami-0335270b14f48b820 \
  --instance-type "$TYPE" --count 1 \
  --key-name kobon-aws --security-group-ids sg-05ab14c684439f96c \
  "${PLACE[@]}" \
  --instance-market-options "MarketType=spot,SpotOptions={MaxPrice=$MAXP,SpotInstanceType=one-time,InstanceInterruptionBehavior=terminate}" \
  --instance-initiated-shutdown-behavior terminate \
  --block-device-mappings "[{\"DeviceName\":\"/dev/sda1\",\"Ebs\":{\"VolumeSize\":$DISK,\"VolumeType\":\"gp3\",\"DeleteOnTermination\":true}}]" \
  --user-data "file://$UD" \
  --tag-specifications "ResourceType=instance,Tags=[{Key=Name,Value=tr-$STAGE},{Key=project,Value=tournament-ramsey}]" \
  --query 'Instances[0].InstanceId' --output text 2>&1) || true
rm -f "$UD"
if [ -n "$DRY" ]; then echo "$OUT" | grep -q DryRunOperation && echo "dry run OK (request valid, nothing created)" || echo "dry run FAILED: $OUT"; exit 0; fi
case "$OUT" in i-*) ;; *) echo "launch failed: $OUT"; exit 1 ;; esac
IID="$OUT"
[ -f results/aws_ledger.csv ] || echo "stage,instance_id,instance_type,max_price,stage_cap,disk_gb,launched_utc" > results/aws_ledger.csv
echo "$STAGE,$IID,$TYPE,$MAXP,$CAP,$DISK,$(date -u +%FT%TZ)" >> results/aws_ledger.csv
aws ec2 wait instance-running --instance-ids "$IID"
IP=$(aws ec2 describe-instances --instance-ids "$IID" --query 'Reservations[0].Instances[0].PublicIpAddress' --output text)
echo "launched $IID at $IP"
cat <<EOF
next (from the Mac, in this repo):
  bash scripts/cloud/push.sh $IP
  ssh -i ~/.ssh/kobon-aws.pem ubuntu@$IP 'cd tr && bash scripts/cloud/setup.sh'
  ssh -i ~/.ssh/kobon-aws.pem ubuntu@$IP 'cd tr && nohup bash scripts/cloud/run_stage.sh $STAGE WORKERS > results/$STAGE.log 2>&1 < /dev/null &'
  nohup bash scripts/cloud/sync_back.sh $IP $STAGE 600 > results/$STAGE.sync.log 2>&1 &
  nohup python3 scripts/cloud/cost_meter.py --enforce --loop 600 > results/aws_meter.log 2>&1 &
EOF
