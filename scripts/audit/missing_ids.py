"""usage: python3 -I missing_ids.py STAGE_DIR NAME OUT.json : UNSAT leaves of NAME with no both_verified cakelog."""
import json, sys, glob, re
sd, name, outp = sys.argv[1].rstrip('/'), sys.argv[2], sys.argv[3]
pat = re.compile(r'/results/[^/]+/([^/]+)/run/tmp/ss_(.+)_[a-z0-9_]{8}/')
both = set()
for f in glob.glob(sd + '/cakelog/*.json'):
    try: r = json.load(open(f))
    except Exception: continue
    m = pat.search(r.get('cnf') or '')
    if m and m.group(1) == name and r.get('both_verified'): both.add(m.group(2).replace('_', '.'))
recs = {}
for line in open(f'{sd}/{name}/run/results.jsonl'):
    r = json.loads(line); recs[r['id']] = r
miss = sorted(i for i, r in recs.items() if r['status'] == 'UNSAT' and i not in both)
json.dump(miss, open(outp, 'w'))
print(name, 'leaves', sum(r['status'] == 'UNSAT' for r in recs.values()), 'missing', len(miss))
