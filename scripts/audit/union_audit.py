"""usage: python3 -I union_audit.py STAGE_DIR RECHECK_DIR [NAME ...]
Every UNSAT leaf (latest record, check VERIFIED) of each instance must be checked by BOTH lrat-check and
cake_lpr: either a both_verified cakelog from the run (STAGE_DIR/cakelog) or a re-check item in
RECHECK_DIR/NAME/items.jsonl with lrat VERIFIED and cake VERIFIED.  Also: no lrat/cake disagreement anywhere."""
import json, sys, glob, os, re, collections
sd, rd = sys.argv[1].rstrip('/'), sys.argv[2].rstrip('/')
names = sys.argv[3:] or sorted(os.path.basename(os.path.dirname(os.path.dirname(p))) for p in glob.glob(sd + '/*/run/results.jsonl'))
pat = re.compile(r'/results/[^/]+/([^/]+)/run/tmp/ss_(.+)_[a-z0-9_]{8}/')
run_both = collections.defaultdict(set); dis = []
for f in glob.glob(sd + '/cakelog/*.json'):
    try: r = json.load(open(f))
    except Exception: dis.append(('UNREADABLE', f)); continue
    m = pat.search(r.get('cnf') or '')
    if not m: continue
    lv = (r.get('lrat') or {}).get('verdict'); cv = (r.get('cake') or {}).get('verdict')
    if lv and cv and (lv == 'VERIFIED') != (cv == 'VERIFIED') and 'heap space' not in str((r.get('cake') or {}).get('said')):
        dis.append((m.group(1), m.group(2), lv, cv))
    if r.get('both_verified'): run_both[m.group(1)].add(m.group(2).replace('_', '.'))
ok_all = True; tl = tb = tr = 0
for n in names:
    recs = {}
    for line in open(f'{sd}/{n}/run/results.jsonl'):
        r = json.loads(line); recs[r['id']] = r
    leaves = {i for i, r in recs.items() if r['status'] == 'UNSAT'}
    notver = {i for i in leaves if recs[i].get('check') != 'VERIFIED'}
    rec_both = set()
    p = f'{rd}/{n}/items.jsonl'
    if os.path.exists(p):
        for line in open(p):
            it = json.loads(line)
            if it.get('lrat') == 'VERIFIED' and it.get('cake') == 'VERIFIED' and it.get('verdict') == 'VERIFIED': rec_both.add(it['id'])
    covered = leaves & (run_both[n] | rec_both)
    miss = sorted(leaves - covered)
    ok = not miss and not notver
    ok_all &= ok
    tl += len(leaves); tb += len(leaves & run_both[n]); tr += len((leaves - run_both[n]) & rec_both)
    print(f'{n}: leaves {len(leaves)} = run-both {len(leaves & run_both[n])} + re-check {len((leaves - run_both[n]) & rec_both)}; missing {len(miss)} {miss[:5]}; check!=VERIFIED {len(notver)}')
print(f'TOTAL leaves {tl}: run-both {tb} + re-check {tr}; disagreements (non-heap) {len(dis)} {dis[:5]}')
print('EVERY LEAF CHECKED BY BOTH lrat-check AND cake_lpr' if ok_all and not dis else 'NOT COMPLETE')
