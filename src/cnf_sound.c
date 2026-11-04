/*
 * cnf_sound.c -- independent soundness check of a direct TT_k-exclusion CNF.
 *
 * Claim checked: every clause of CNF is satisfied by every TT_k-free
 * completion of the partial tournament MATRIX.  Then "CNF is UNSAT" implies
 * "MATRIX has no TT_k-free completion" (completeness of the encoding is not
 * needed for that direction and is not checked).
 *
 * MATRIX: n x n '0' '1' '*' tokens, upper triangle authoritative ('1' at
 * (i,j), i<j: i->j; '0': j->i; '*': free), as in the Neiman-Mackey-Heule files.
 *
 * Variable numbering (--numbering):
 *   nmh  (default) NMH encoding/tour-encode.c: vertices 1..n, pair a<b has
 *        variable a + (b-2)(b-1)/2, true iff a->b.  Variables above n(n-1)/2
 *        are NMH's 3-cycle variables; any literal on them is reported as
 *        UNSUPPORTED (the direct encodings used here never contain one).
 *   free build/encode: the free pairs i<j (0-based) in row-major order of the
 *        upper triangle are variables 1..F, true iff i->j; variables above F
 *        are UNSUPPORTED.
 *
 * A clause C is accepted if
 *   (a) some literal is true on a fixed arc of MATRIX (this covers NMH's unit
 *       clauses, which must agree with MATRIX), or
 *   (b) C contains l and -l, or
 *   (c) after dropping literals that are false on fixed arcs, let alpha be the
 *       orientation of the remaining (free) pairs that falsifies C; there is a
 *       k-set S of vertices containing every endpoint of alpha such that EVERY
 *       orientation of the free pairs inside S that extends alpha makes S
 *       transitive.  (Then every completion falsifying C contains the TT_k S.
 *       If alpha is empty, S must be a TT_k of fixed arcs: no completion is
 *       TT_k-free and C holds vacuously.)
 * Anything else is reported as FAIL (the checker is sufficient, not complete).
 *
 * usage: cnf_sound MATRIX k CNF [--numbering nmh|free] [--quiet]
 * Prints counts per case and "SOUND" (exit 0) or "NOT SOUND"/errors (exit 1).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 64

static int n, k;
static int fx[MAXN][MAXN];          /* +1: i->j fixed, -1: j->i fixed, 0: free */
static int *va, *vb;                /* var -> pair (va < vb), 0-based */
static int nv_arcs;                 /* number of arc variables */

static void die(const char *m) { fprintf(stderr, "cnf_sound: %s\n", m); exit(2); }

static void read_matrix(const char *path) {
  FILE *in = fopen(path, "r");
  if (!in) { perror(path); exit(2); }
  static char cell[MAXN * MAXN];
  char tok[16]; int cells = 0;
  while (fscanf(in, "%15s", tok) == 1) {
    if (cells >= MAXN * MAXN) die("matrix too big");
    cell[cells++] = tok[0];
  }
  fclose(in);
  n = 0; while (n * n < cells) n++;
  if (n * n != cells) die("matrix not square");
  for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) {
    char c = cell[i * n + j];
    if (c == '1') { fx[i][j] = 1; fx[j][i] = -1; }
    else if (c == '0') { fx[i][j] = -1; fx[j][i] = 1; }
    else if (c == '*') { fx[i][j] = fx[j][i] = 0; }
    else die("bad matrix cell");
  }
}

/* S[0..k-1], orientation or_[x][y] = 1 if x->y (only for x,y in S) */
static int S[16], inS[MAXN];
static int ori[MAXN][MAXN];

static int transitive_now(void) {
  int seen = 0;
  for (int i = 0; i < k; i++) {
    int d = 0;
    for (int j = 0; j < k; j++) if (j != i && ori[S[i]][S[j]] == 1) d++;
    if (seen >> d & 1) return 0;
    seen |= 1 << d;
  }
  return 1;
}

/* alpha: forced orientation on some free pairs (alpha[x][y] = 1 if x->y forced) */
static int alpha[MAXN][MAXN];

/* every orientation of free pairs in S not fixed by alpha makes S transitive? */
static int forced_transitive(void) {
  int fu[64], fv[64], nf = 0;
  for (int i = 0; i < k; i++) for (int j = i + 1; j < k; j++) {
    int x = S[i], y = S[j];
    if (fx[x][y] == 1) { ori[x][y] = 1; ori[y][x] = 0; }
    else if (fx[x][y] == -1) { ori[x][y] = 0; ori[y][x] = 1; }
    else if (alpha[x][y]) { ori[x][y] = 1; ori[y][x] = 0; }
    else if (alpha[y][x]) { ori[x][y] = 0; ori[y][x] = 1; }
    else { fu[nf] = x; fv[nf] = y; nf++; }
  }
  if (nf > 24) return 0;
  for (uint32_t m = 0; m < (1u << nf); m++) {
    for (int b = 0; b < nf; b++) {
      int x = fu[b], y = fv[b], o = (m >> b) & 1;
      ori[x][y] = o; ori[y][x] = !o;
    }
    if (!transitive_now()) return 0;
  }
  return 1;
}

static int base[MAXN], nbase;
/* choose k - nbase extra vertices (outside base), ascending, try each S */
static int extend_rec(int need, int start, int pos) {
  if (need == 0) return forced_transitive();
  for (int x = start; x < n; x++) {
    if (inS[x]) continue;
    S[pos] = x; inS[x] = 1;
    int r = extend_rec(need - 1, x + 1, pos + 1);
    inS[x] = 0;
    if (r) return 1;
  }
  return 0;
}

int main(int argc, char **argv) {
  if (argc < 4) { fprintf(stderr, "usage: cnf_sound MATRIX k CNF [--numbering nmh|free] [--quiet]\n"); return 2; }
  int nmh = 1, quiet = 0;
  for (int i = 4; i < argc; i++) {
    if (!strcmp(argv[i], "--numbering") && i + 1 < argc) { nmh = !strcmp(argv[++i], "nmh"); }
    else if (!strcmp(argv[i], "--quiet")) quiet = 1;
    else die("unknown option");
  }
  read_matrix(argv[1]);
  k = atoi(argv[2]);
  if (k < 3 || k > 12) die("k out of range");
  int npairs = n * (n - 1) / 2;
  va = calloc(npairs + 1, sizeof(int)); vb = calloc(npairs + 1, sizeof(int));
  if (nmh) {
    for (int b = 2; b <= n; b++) for (int a = 1; a < b; a++) {
      int v = a + (b - 2) * (b - 1) / 2;
      va[v] = a - 1; vb[v] = b - 1;
    }
    nv_arcs = npairs;
  } else {
    nv_arcs = 0;
    for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++)
      if (fx[i][j] == 0) { nv_arcs++; va[nv_arcs] = i; vb[nv_arcs] = j; }
  }
  FILE *in = fopen(argv[3], "r");
  if (!in) { perror(argv[3]); return 2; }
  long long hv = -1, hc = -1;
  int c;
  /* header (skip comment lines) */
  for (;;) {
    c = fgetc(in);
    if (c == 'c') { while ((c = fgetc(in)) != '\n' && c != EOF) {} continue; }
    if (c != 'p') die("no 'p cnf' header");
    if (fscanf(in, " cnf %lld %lld", &hv, &hc) != 2) die("bad header");
    break;
  }
  long long ncls = 0, n_fixed_true = 0, n_taut = 0, n_fail = 0, n_unsup = 0, maxvar = 0;
  long long n_wit[16] = {0};          /* witnesses by number of endpoints of alpha */
  int lits[4096], nl = 0, lit;
  while (fscanf(in, "%d", &lit) == 1) {
    if (lit != 0) {
      if (nl >= 4096) die("clause too long");
      lits[nl++] = lit;
      long long a = lit < 0 ? -(long long)lit : lit;
      if (a > maxvar) maxvar = a;
      continue;
    }
    ncls++;
    /* classify */
    int sat = 0, taut = 0, unsup = 0;
    int ax[64], ay[64], na = 0;      /* alpha arcs x->y */
    for (int i = 0; i < nl && !sat && !unsup; i++) {
      int v = abs(lits[i]);
      if (v > nv_arcs) { unsup = 1; break; }
      int u = va[v], w = vb[v];
      int tu = lits[i] > 0 ? u : w, tw = lits[i] > 0 ? w : u;   /* literal true iff tu->tw */
      if (fx[tu][tw] == 1) { sat = 1; break; }
      if (fx[tu][tw] == -1) continue;                           /* false on a fixed arc */
      /* falsifying orientation: tw -> tu */
      int dup = 0;
      for (int j = 0; j < na; j++) {
        if (ax[j] == tw && ay[j] == tu) dup = 1;
        if (ax[j] == tu && ay[j] == tw) taut = 1;
      }
      if (taut) break;
      if (!dup) { if (na >= 64) { unsup = 1; break; } ax[na] = tw; ay[na] = tu; na++; }
    }
    nl = 0;
    if (unsup) { n_unsup++; if (!quiet && n_unsup <= 5) fprintf(stderr, "UNSUPPORTED clause %lld\n", ncls); continue; }
    if (sat) { n_fixed_true++; continue; }
    if (taut) { n_taut++; continue; }
    /* endpoints */
    nbase = 0;
    memset(inS, 0, sizeof inS);
    int toomany = 0;
    for (int j = 0; j < na && !toomany; j++) {
      int e[2] = {ax[j], ay[j]};
      for (int t = 0; t < 2; t++) if (!inS[e[t]]) {
        if (nbase >= k) { toomany = 1; break; }
        inS[e[t]] = 1; base[nbase++] = e[t];
      }
    }
    int ok = 0;
    if (!toomany) {   /* na == 0: the fixed arcs alone must contain a TT_k */
      for (int j = 0; j < na; j++) { alpha[ax[j]][ay[j]] = 1; }
      for (int i = 0; i < nbase; i++) S[i] = base[i];
      ok = extend_rec(k - nbase, 0, nbase);
      for (int j = 0; j < na; j++) { alpha[ax[j]][ay[j]] = 0; }
    }
    if (ok) n_wit[nbase]++;
    else {
      n_fail++;
      if (!quiet && n_fail <= 5) fprintf(stderr, "FAIL clause %lld (%d free literals, %d vertices)\n", ncls, na, toomany ? -1 : nbase);
    }
  }
  fclose(in);
  int bad_header = (hc != ncls) || (maxvar > hv);
  printf("n=%d k=%d numbering=%s header=%lld/%lld clauses_read=%lld maxvar=%lld%s\n", n, k, nmh ? "nmh" : "free",
         hv, hc, ncls, maxvar, bad_header ? " HEADER MISMATCH" : "");
  printf("satisfied_by_fixed_arcs=%lld tautologies=%lld", n_fixed_true, n_taut);
  long long tw = 0;
  for (int i = 0; i <= k; i++) { tw += n_wit[i]; if (n_wit[i]) printf(" witness_v%d=%lld", i, n_wit[i]); }
  printf(" witnessed=%lld unsupported=%lld fail=%lld\n", tw, n_unsup, n_fail);
  int good = !bad_header && n_fail == 0 && n_unsup == 0;
  printf("%s\n", good ? "SOUND" : "NOT SOUND");
  return good ? 0 : 1;
}
