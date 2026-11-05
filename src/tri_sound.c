/* tri_sound.c -- independent soundness check of a TT_k-exclusion CNF in 3-cycle mode.
 *
 * INDEPENDENT AUDIT TOOL.  Written on 5 Nov 2026 by an external auditor without using
 * src/encode.c or src/cnf_sound.c, and kept separate from them on purpose: do not merge its
 * logic into the repository's own tools.  It exists because src/cnf_sound.c cannot check the
 * Stage 3 CNFs: those come from build/encode with ordering limit 1, which writes "some triple of
 * S is a 3-cycle" clauses over auxiliary 3-cycle variables, and cnf_sound reports every literal
 * on a variable above F as UNSUPPORTED.
 *
 * Variables: the "free" arc variables 1..F (the '*' pairs i<j of MATRIX in row-major order of the
 * upper triangle, true iff i->j, as build/encode numbers them; or NMH's numbering with the
 * optional 4th argument "nmh") plus auxiliary variables above F.
 * Interpretation of an auxiliary variable t, derived from the CNF itself (pass 1): if -t occurs
 * only in clauses whose other literals are arc literals on one triple {a,b,c}, t := "triple
 * {a,b,c} is cyclic"; if -t never occurs, t := TRUE; anything else makes t "bad" (NOT SOUND).
 * Claim checked (pass 2): under that interpretation every clause holds in every TT_k-free
 * completion of MATRIX.  Then "CNF is UNSAT" implies "MATRIX has no TT_k-free completion".
 * A clause is accepted if it is satisfied by a fixed arc or a constant-true variable, is a
 * tautology, is vacuous (no orientation of the free pairs among its vertices falsifies it
 * when they are fewer than k), or every completion falsifying it contains a TT_k on some k-set
 * S containing its vertices (shortcut: every triple of S not named positively is forced
 * acyclic; else brute force over the free pairs inside S, at most 22).  Also required: the
 * header's clause count equals the number of clauses and no variable exceeds the header's.
 *
 * usage: tri_sound MATRIX k CNF [nmh]
 *   MATRIX: n x n tokens '0' '1' '*' (n <= 64), upper triangle authoritative, as for build/encode.
 * Output: a statistics line, a counts line, then "SOUND" (exit 0) or "NOT SOUND" (exit 1); the
 * first five failing clauses go to stderr; exit 2 or 3 on unreadable or malformed input.
 * Build: cc -O2 -o build/tri_sound src/tri_sound.c      Tests: python3 tests/test_tri_sound.py
 * Used by scripts/cloud/run_stage.sh (stage3) on every Stage 3 CNF before it is solved.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 64
static int n, K, F;
static int fx[MAXN][MAXN];
static int va[4096], vb[4096];
static int (*tri)[3]; static int *tkind; /* 0 unseen, 1 triple, 2 const true, 3 bad */
static int maxv;

static FILE *in; static char buf[1 << 22]; static size_t bl, bp;
static int gc(void) { if (bp == bl) { bl = fread(buf, 1, sizeof buf, in); bp = 0; if (!bl) return -1; } return buf[bp++]; }
static int readint(int *x) {
  int c = gc();
  while (c == ' ' || c == '\n' || c == '\r' || c == '\t') c = gc();
  if (c == -1) return 0;
  int s = 1; if (c == '-') { s = -1; c = gc(); }
  if (c < '0' || c > '9') { fprintf(stderr, "parse error char %d\n", c); exit(3); }
  int v = 0; while (c >= '0' && c <= '9') { v = v * 10 + (c - '0'); c = gc(); }
  *x = s * v; return 1;
}
static long long hv, hc;
static void open_cnf(const char *p) {
  in = fopen(p, "r"); if (!in) { perror(p); exit(2); }
  bl = bp = 0;
  char line[256];
  /* header line read via gc */
  int c, i = 0; while ((c = gc()) != '\n' && c != -1 && i < 255) line[i++] = c; line[i] = 0;
  if (sscanf(line, "p cnf %lld %lld", &hv, &hc) != 2) { fprintf(stderr, "bad header %s\n", line); exit(2); }
}

static int lits[8192], nl;
static int readclause(void) {
  nl = 0; int x;
  while (readint(&x)) { if (x == 0) return 1; if (nl >= 8192) { fprintf(stderr, "long\n"); exit(2);} lits[nl++] = x; }
  if (nl) { fprintf(stderr, "unterminated clause at EOF\n"); exit(2); }
  return 0;
}

/* orientation state for check: o[u][v] = 1 if u->v, -1 if v->u, 0 unknown */
static int o[MAXN][MAXN];
static int cyc3(int a, int b, int c) { /* given full orientation in o: 1 if cyclic */
  int da = (o[a][b] == 1) + (o[a][c] == 1);
  return da == 1 && ((o[b][c] == 1) + (o[b][a] == 1)) == 1;
}
static int tposA[64][3], ntpos, tnegA[64][3], ntneg;
static int Sv[16], ns;
static int inU[MAXN];

/* is triple forced acyclic given o (fixed + alpha), enumerating its unknown pairs */
static int forced_acyclic(int a, int b, int c) {
  int p[3][2] = {{a, b}, {a, c}, {b, c}}, fr[3], nf = 0;
  for (int i = 0; i < 3; i++) if (o[p[i][0]][p[i][1]] == 0) fr[nf++] = i;
  for (int m = 0; m < (1 << nf); m++) {
    for (int j = 0; j < nf; j++) { int u = p[fr[j]][0], v = p[fr[j]][1]; int d = (m >> j & 1) ? 1 : -1; o[u][v] = d; o[v][u] = -d; }
    int cy = cyc3(a, b, c);
    for (int j = 0; j < nf; j++) { int u = p[fr[j]][0], v = p[fr[j]][1]; o[u][v] = o[v][u] = 0; }
    if (cy) return 0;
  }
  return 1;
}
static int is_tpos(int a, int b, int c) {
  int s[3] = {a, b, c}, t;
  if (s[0] > s[1]) { t = s[0]; s[0] = s[1]; s[1] = t; }
  if (s[1] > s[2]) { t = s[1]; s[1] = s[2]; s[2] = t; }
  if (s[0] > s[1]) { t = s[0]; s[0] = s[1]; s[1] = t; }
  for (int i = 0; i < ntpos; i++) if (tposA[i][0] == s[0] && tposA[i][1] == s[1] && tposA[i][2] == s[2]) return 1;
  return 0;
}
static long long n_shortcut, n_brute, n_vacuous, n_ext;
/* every orientation of unknown pairs inside S satisfying the falsify conditions makes S transitive? */
static int check_S(void) {
  /* shortcut: all triples forced acyclic */
  int ok = 1;
  for (int i = 0; i < ns && ok; i++) for (int j = i + 1; j < ns && ok; j++) for (int l = j + 1; l < ns && ok; l++) {
    if (is_tpos(Sv[i], Sv[j], Sv[l])) continue;
    if (!forced_acyclic(Sv[i], Sv[j], Sv[l])) ok = 0;
  }
  if (ok) { n_shortcut++; return 1; }
  /* brute force */
  int fu[64], fv[64], nf = 0;
  for (int i = 0; i < ns; i++) for (int j = i + 1; j < ns; j++) if (o[Sv[i]][Sv[j]] == 0) { fu[nf] = Sv[i]; fv[nf] = Sv[j]; nf++; }
  if (nf > 22) return 0;
  int res = 1;
  for (uint32_t m = 0; m < (1u << nf) && res; m++) {
    for (int b = 0; b < nf; b++) { int d = (m >> b & 1) ? 1 : -1; o[fu[b]][fv[b]] = d; o[fv[b]][fu[b]] = -d; }
    int fals = 1;
    for (int i = 0; i < ntpos && fals; i++) if (cyc3(tposA[i][0], tposA[i][1], tposA[i][2])) fals = 0;
    for (int i = 0; i < ntneg && fals; i++) if (!cyc3(tnegA[i][0], tnegA[i][1], tnegA[i][2])) fals = 0;
    if (fals) {
      /* transitive iff out-degrees within S distinct */
      int seen = 0;
      for (int i = 0; i < ns; i++) { int d = 0; for (int j = 0; j < ns; j++) if (j != i && o[Sv[i]][Sv[j]] == 1) d++; if (seen >> d & 1) { res = 0; break; } seen |= 1 << d; }
    }
  }
  for (int b = 0; b < nf; b++) o[fu[b]][fv[b]] = o[fv[b]][fu[b]] = 0;
  n_brute++;
  return res;
}
static int Ubase[16], nU;
static int ext(int need, int start) {
  if (need == 0) return check_S();
  for (int x = start; x < n; x++) {
    if (inU[x]) continue;
    Sv[ns++] = x; inU[x] = 1;
    int r = ext(need - 1, x + 1);
    ns--; inU[x] = 0;
    if (r) return 1;
  }
  return 0;
}
/* vacuity: no orientation of unknown pairs among U satisfies falsify conditions */
static int vacuous(void) {
  int fu[64], fv[64], nf = 0;
  for (int i = 0; i < nU; i++) for (int j = i + 1; j < nU; j++) if (o[Ubase[i]][Ubase[j]] == 0) { fu[nf] = Ubase[i]; fv[nf] = Ubase[j]; nf++; }
  if (nf > 22) return 0;
  int vac = 1;
  for (uint32_t m = 0; m < (1u << nf) && vac; m++) {
    for (int b = 0; b < nf; b++) { int d = (m >> b & 1) ? 1 : -1; o[fu[b]][fv[b]] = d; o[fv[b]][fu[b]] = -d; }
    int fals = 1;
    for (int i = 0; i < ntpos && fals; i++) if (cyc3(tposA[i][0], tposA[i][1], tposA[i][2])) fals = 0;
    for (int i = 0; i < ntneg && fals; i++) if (!cyc3(tnegA[i][0], tnegA[i][1], tnegA[i][2])) fals = 0;
    if (fals) vac = 0;
  }
  for (int b = 0; b < nf; b++) o[fu[b]][fv[b]] = o[fv[b]][fu[b]] = 0;
  return vac;
}

int main(int argc, char **argv) {
  if (argc < 4) { fprintf(stderr, "usage\n"); return 2; }
  FILE *mf = fopen(argv[1], "r"); char tok[16]; static char cell[MAXN * MAXN]; int cells = 0;
  while (fscanf(mf, "%15s", tok) == 1) cell[cells++] = tok[0];
  fclose(mf);
  while (n * n < cells) n++;
  if (n * n != cells) { fprintf(stderr, "not square\n"); return 2; }
  K = atoi(argv[2]);
  for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) {
    char c = cell[i * n + j];
    if (c == '1') { fx[i][j] = 1; fx[j][i] = -1; } else if (c == '0') { fx[i][j] = -1; fx[j][i] = 1; }
    else if (c == '*') { fx[i][j] = fx[j][i] = 0; va[++F] = i; vb[F] = j; } else { fprintf(stderr, "bad cell\n"); return 2; }
  }
  if (argc > 4 && !strcmp(argv[4], "nmh")) {
    F = n * (n - 1) / 2;
    for (int b = 2; b <= n; b++) for (int a = 1; a < b; a++) { int v = a + (b - 2) * (b - 1) / 2; va[v] = a - 1; vb[v] = b - 1; }
  }
  /* pass 1: derive triples */
  open_cnf(argv[3]);
  long long nc = 0, ncomplex = 0;
  int cap = 1 << 20;
  tri = calloc(cap, sizeof *tri); tkind = calloc(cap, sizeof(int));
  int (*vs)[4] = calloc(cap, sizeof *vs); /* up to 3 vertices + count; [3] = count */
  while (readclause()) {
    nc++;
    int negt = 0, tv = 0, other_t = 0;
    for (int i = 0; i < nl; i++) {
      int v = abs(lits[i]); if (v > maxv) maxv = v;
      if (v >= cap) { fprintf(stderr, "var too big\n"); return 2; }
      if (v > F) { if (lits[i] < 0) { negt++; tv = v; } else other_t++; }
    }
    if (negt == 0) continue;
    if (negt > 1 || other_t) { ncomplex++; continue; }
    for (int i = 0; i < nl; i++) {
      int v = abs(lits[i]); if (v > F) continue;
      int e[2] = {va[v], vb[v]};
      for (int q = 0; q < 2; q++) {
        int found = 0; for (int r = 0; r < vs[tv][3]; r++) if (vs[tv][r] == e[q]) found = 1;
        if (!found) { if (vs[tv][3] < 3) vs[tv][vs[tv][3]++] = e[q]; else tkind[tv] = 3; }
      }
    }
    if (tkind[tv] != 3) tkind[tv] = 1;
  }
  fclose(in);
  long long nt = 0, ntrue = 0, nbad = 0;
  for (int t = F + 1; t <= maxv; t++) {
    if (tkind[t] == 0) { tkind[t] = 2; ntrue++; continue; }
    if (tkind[t] == 3 || vs[t][3] != 3) { tkind[t] = 3; nbad++; continue; }
    int s[3] = {vs[t][0], vs[t][1], vs[t][2]}, x;
    if (s[0] > s[1]) { x = s[0]; s[0] = s[1]; s[1] = x; }
    if (s[1] > s[2]) { x = s[1]; s[1] = s[2]; s[2] = x; }
    if (s[0] > s[1]) { x = s[0]; s[0] = s[1]; s[1] = x; }
    memcpy(tri[t], s, sizeof s); nt++;
  }
  printf("n=%d k=%d F=%d header=%lld/%lld clauses=%lld maxvar=%d tvars: triple=%lld consttrue=%lld bad=%lld complex_neg_clauses=%lld\n",
         n, K, F, hv, hc, nc, maxv, nt, ntrue, nbad, ncomplex);
  /* pass 2 */
  open_cnf(argv[3]);
  for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) o[i][j] = fx[i][j];
  long long nsat = 0, ntaut = 0, nok = 0, nfail = 0, nidx = 0;
  int ax[8192], ay[8192];
  while (readclause()) {
    nidx++;
    int sat = 0, taut = 0, na = 0, bad = 0; ntpos = ntneg = 0;
    for (int i = 0; i < nl && !sat && !taut && !bad; i++) {
      int v = abs(lits[i]);
      if (v <= F) {
        int u = va[v], w = vb[v];
        int tu = lits[i] > 0 ? u : w, tw = lits[i] > 0 ? w : u; /* lit true iff tu->tw; falsified: tw->tu */
        if (fx[tu][tw] == 1) { sat = 1; break; }
        if (fx[tu][tw] == -1) continue;
        if (o[tw][tu] == 1) continue; /* already falsified by alpha (duplicate) */
        if (o[tu][tw] == 1) { taut = 1; break; }
        o[tw][tu] = 1; o[tu][tw] = -1; ax[na] = tw; ay[na] = tu; na++;
      } else {
        if (tkind[v] == 2) { if (lits[i] > 0) sat = 1; continue; }
        if (tkind[v] != 1) { bad = 1; break; }
        if (lits[i] > 0) { if (ntpos >= 64) { bad = 1; break; } memcpy(tposA[ntpos++], tri[v], sizeof(int) * 3); }
        else { if (ntneg >= 64) { bad = 1; break; } memcpy(tnegA[ntneg++], tri[v], sizeof(int) * 3); }
      }
    }
    int ok = 0;
    if (sat) { nsat++; ok = 1; }
    else if (taut) { ntaut++; ok = 1; }
    else if (!bad) {
      nU = 0; memset(inU, 0, sizeof inU);
      #define ADDU(x) do { if (!inU[x]) { inU[x] = 1; if (nU < 16) Ubase[nU] = x; nU++; } } while (0)
      for (int j = 0; j < na; j++) { ADDU(ax[j]); ADDU(ay[j]); }
      for (int j = 0; j < ntpos; j++) for (int q = 0; q < 3; q++) ADDU(tposA[j][q]);
      for (int j = 0; j < ntneg; j++) for (int q = 0; q < 3; q++) ADDU(tnegA[j][q]);
      if (nU <= K) {
        if (nU < K && vacuous()) { ok = 1; n_vacuous++; }
        else {
          ns = 0; for (int j = 0; j < nU; j++) Sv[ns++] = Ubase[j];
          if (nU < K) n_ext++;
          ok = ext(K - nU, 0);
        }
      }
      for (int j = 0; j < nU && j < 16; j++) inU[Ubase[j]] = 0;
    }
    for (int j = 0; j < na; j++) { o[ax[j]][ay[j]] = 0; o[ay[j]][ax[j]] = 0; }
    if (ok) nok++; else { nfail++; if (nfail <= 5) { fprintf(stderr, "FAIL clause %lld:", nidx); for (int i = 0; i < nl; i++) fprintf(stderr, " %d", lits[i]); fprintf(stderr, "\n"); } }
  }
  int good = nfail == 0 && nbad == 0 && hc == nidx && maxv <= hv;
  printf("satisfied=%lld tautologies=%lld ok=%lld (shortcut=%lld brute=%lld vacuous=%lld extended=%lld) fail=%lld\n",
         nsat, ntaut, nok, n_shortcut, n_brute, n_vacuous, n_ext, nfail);
  printf("%s\n", good ? "SOUND" : "NOT SOUND");
  return good ? 0 : 1;
}
