"""usage: python3 -I jsonl_check.py TIMEOUTS RUN_DIR...   (TIMEOUTS e.g. 600,1800,0)
Every line of RUN_DIR/results.jsonl must parse; flags records a kill could have produced:
UNKNOWN faster than 95% of its level's time limit (or at a level with no limit), UNSAT whose check
is not VERIFIED, any other status.  Prints line counts; exit 1 if anything is flagged."""
import json, sys
tl = [int(x) for x in sys.argv[1].split(',')]
bad = 0
for d in sys.argv[2:]:
    n = 0; flags = []
    for i, line in enumerate(open(d.rstrip('/') + '/results.jsonl'), 1):
        try: r = json.loads(line)
        except ValueError: flags.append((i, 'UNPARSEABLE', line[:80])); continue
        n += 1
        lim = tl[min(r['level'], len(tl) - 1)]
        if r['status'] == 'UNKNOWN' and (lim == 0 or r['secs'] < 0.95 * lim): flags.append((i, 'FAST UNKNOWN', r['id'], r['secs']))
        elif r['status'] == 'UNSAT' and r.get('check') != 'VERIFIED': flags.append((i, 'UNSAT not VERIFIED', r['id'], r.get('check')))
        elif r['status'] not in ('UNSAT', 'UNKNOWN'): flags.append((i, 'STATUS', r['id'], r['status']))
    bad += len(flags)
    print(d, 'lines', n, 'flags', len(flags), flags[:5])
sys.exit(1 if bad else 0)
