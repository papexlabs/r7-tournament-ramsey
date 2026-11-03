/*
 * encode.c -- CNF for "no transitive subtournament TT_k" on a partial tournament.
 *
 * Input: an n x n matrix of '0' '1' '*' (whitespace separated, n <= 64).
 * Only the upper triangle is read: entry (i,j), j>i, is '1' if i->j, '0' if
 * j->i, '*' if free (same convention as the Neiman-Mackey-Heule files).
 *
 * Variables: one per free pair {i<j}, true iff i->j; numbered 1..F in
 * row-major order of the upper triangle.  Extra "3-cycle" variables are
 * created on demand (t -> triple is cyclic; only this direction is needed
 * because t occurs only positively in the TT_k clauses).
 *
 * For every k-subset S of vertices:
 *   - skipped if S contains a fully fixed 3-cycle (cannot be transitive);
 *   - otherwise the orderings of S compatible with the fixed arcs are
 *     enumerated (up to limit+1).  0 orderings -> skipped.
 *   - <= limit orderings: the set of forbidden assignments of the free pairs
 *     inside S is turned into its prime implicants (Quine-McCluskey merge),
 *     one clause per prime implicant (propagation complete per k-set);
 *   - > limit orderings: one clause "some triple of S is a 3-cycle" over
 *     3-cycle literals (fixed-acyclic triples dropped, single-free-arc
 *     triples replaced by the arc literal).
 *
 * usage: encode MATRIX k limit OUT.cnf [MAP.txt] [--count]
 *   --count : only count clauses / literals, write nothing.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 64
#define TRUE_LIT  0x7fffffff
#define FALSE_LIT (-0x7fffffff)

static int n, k, limit, count_only;
static int fx[MAXN][MAXN];      /* +1: i->j fixed, -1: j->i fixed, 0 free */
static int avar[MAXN][MAXN];    /* var of free pair (min,max), else 0 */
static int nvars;
static int *tvar;               /* 3-cycle var per triple index, lazily */
static FILE *body, *mapf;
static long long ncls, nlits, n_ksets_skip_cyc, n_ksets_zero, n_ksets_direct, n_ksets_tri;
static long long ncls_direct, ncls_tri, ncls_tdef;

/* literal for "u -> v" */
static int lit(int u, int v) {
  if (fx[u][v] == 1) return TRUE_LIT;
  if (fx[u][v] == -1) return FALSE_LIT;
  int a = u < v ? u : v, b = u < v ? v : u;
  return (u < v) ? avar[a][b] : -avar[a][b];
}

static int clsbuf[4096], clslen, clssat;
static void cls_begin(void) { clslen = 0; clssat = 0; }
static void cls_add(int l) {
  if (l == TRUE_LIT) { clssat = 1; return; }
  if (l == FALSE_LIT) return;
  for (int i = 0; i < clslen; i++) {
    if (clsbuf[i] == l) return;
    if (clsbuf[i] == -l) { clssat = 1; return; }
  }
  clsbuf[clslen++] = l;
}
static int cls_end(void) {   /* returns 1 if a clause was emitted */
  if (clssat) return 0;
  if (clslen == 0) { fprintf(stderr, "c WARNING: empty clause (fixed part already contains TT_%d)\n", k); }
  ncls++; nlits += clslen;
  if (!count_only) {
    for (int i = 0; i < clslen; i++) fprintf(body, "%d ", clsbuf[i]);
    fputs("0\n", body);
  }
  return 1;
}

static long tri_index(int a, int b, int c) { /* a<b<c */
  return (long)a * MAXN * MAXN + (long)b * MAXN + c;
}

/* 3-cycle literal of triple {a,b,c}; TRUE/FALSE if determined. */
static int cyc_lit(int a, int b, int c) {
  /* sort */
  int t;
  if (a > b) { t = a; a = b; b = t; }
  if (b > c) { t = b; b = c; c = t; }
  if (a > b) { t = a; a = b; b = t; }
  int v[3] = {a, b, c};
  /* fixed-acyclic: some vertex has both arcs fixed out, or both fixed in */
  for (int i = 0; i < 3; i++) {
    int x = v[i], y = v[(i + 1) % 3], z = v[(i + 2) % 3];
    if (fx[x][y] == 1 && fx[x][z] == 1) return FALSE_LIT;
    if (fx[x][y] == -1 && fx[x][z] == -1) return FALSE_LIT;
  }
  int nfree = (fx[a][b] == 0) + (fx[a][c] == 0) + (fx[b][c] == 0);
  if (nfree == 0) return TRUE_LIT;  /* fixed and not acyclic => cyclic */
  if (nfree == 1) {
    /* the two fixed arcs form a path x->y->z; cyclic iff z->x */
    int x = -1, y = -1, z = -1;
    for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) for (int l = 0; l < 3; l++) {
      if (i == j || j == l || i == l) continue;
      if (fx[v[i]][v[j]] == 1 && fx[v[j]][v[l]] == 1) { x = v[i]; y = v[j]; z = v[l]; }
    }
    if (x < 0) { fprintf(stderr, "internal: path not found\n"); exit(2); }
    (void)y;
    return lit(z, x);
  }
  long id = tri_index(a, b, c);
  if (tvar[id]) return tvar[id];
  int tv = ++nvars;
  tvar[id] = tv;
  if (mapf && !count_only) fprintf(mapf, "%d t %d %d %d\n", tv, a, b, c);
  /* t & (x->y) -> (y->z) for both cyclic orientations */
  int cyc[2][3] = {{a, b, c}, {a, c, b}};
  for (int o = 0; o < 2; o++)
    for (int i = 0; i < 3; i++) {
      int x = cyc[o][i], y = cyc[o][(i + 1) % 3], z = cyc[o][(i + 2) % 3];
      cls_begin(); cls_add(-tv); cls_add(-lit(x, y)); cls_add(lit(y, z));
      if (cls_end()) ncls_tdef++;
    }
  return tv;
}

/* ---------------- orderings compatible with fixed arcs ------------------ */
static int S[16];
static int ord_[16];
static uint32_t pts[6000];
static int npts;
static int fpu[64], fpv[64], nfp;   /* free pairs inside S (u<v) */

static void ext_rec(int depth, uint32_t remaining) {
  if (npts > limit) return;
  if (depth == k) {
    /* build point: bit b = 1 iff fpu[b] -> fpv[b] (min -> max) */
    int pos[MAXN];
    for (int i = 0; i < k; i++) pos[ord_[i]] = i;
    uint32_t p = 0;
    for (int b = 0; b < nfp; b++) if (pos[fpu[b]] < pos[fpv[b]]) p |= 1u << b;
    pts[npts++] = p;
    return;
  }
  for (int i = 0; i < k; i++) {
    if (!(remaining >> i & 1)) continue;
    int x = S[i], ok = 1;
    for (int j = 0; j < k && ok; j++)
      if (j != i && (remaining >> j & 1) && fx[S[j]][x] == 1) ok = 0;
    if (!ok) continue;
    ord_[depth] = x;
    ext_rec(depth + 1, remaining & ~(1u << i));
    if (npts > limit) return;
  }
}

/* ---------------- Quine-McCluskey prime implicants ---------------------- */
typedef struct { uint32_t val, care; } cube_t;
static cube_t *lvl, *nxt;
static char *merged;
static uint64_t *ht; static int htsz;

static int ht_find(uint64_t key) {
  uint64_t h = key * 0x9E3779B97F4A7C15ULL;
  int i = (int)(h >> 40) & (htsz - 1);
  while (ht[i]) { if (ht[i] == key + 1) return i; i = (i + 1) & (htsz - 1); }
  return -1 - i;
}

static void emit_prime(uint32_t val, uint32_t care) {
  cls_begin();
  for (int b = 0; b < nfp; b++) {
    if (!(care >> b & 1)) continue;
    int u = fpu[b], v = fpv[b];
    int l = lit(u, v);       /* "u->v", u<v */
    cls_add((val >> b & 1) ? -l : l);
  }
  if (cls_end()) ncls_direct++;
}

static void qm(void) {
  int cnt = npts;
  uint32_t full = (nfp == 32) ? 0xffffffffu : ((1u << nfp) - 1);
  for (int i = 0; i < cnt; i++) { lvl[i].val = pts[i]; lvl[i].care = full; }
  while (cnt > 0) {
    /* hash current level */
    htsz = 1; while (htsz < 4 * cnt) htsz <<= 1;
    memset(ht, 0, sizeof(uint64_t) * htsz);
    for (int i = 0; i < cnt; i++) {
      uint64_t key = ((uint64_t)lvl[i].care << 32) | lvl[i].val;
      int r = ht_find(key);
      if (r < 0) ht[-1 - r] = key + 1;
      merged[i] = 0;
    }
    int ncnt = 0;
    /* second hash for next level dedupe: reuse by collecting then sorting */
    for (int i = 0; i < cnt; i++) {
      uint32_t care = lvl[i].care, val = lvl[i].val;
      for (int b = 0; b < nfp; b++) {
        if (!(care >> b & 1)) continue;
        uint64_t key = ((uint64_t)care << 32) | (val ^ (1u << b));
        if (ht_find(key) >= 0) {
          merged[i] = 1;
          if (!(val >> b & 1)) { /* add once: from the partner with bit 0 */
            nxt[ncnt].val = val & ~(1u << b);
            nxt[ncnt].care = care & ~(1u << b);
            ncnt++;
          }
        }
      }
    }
    for (int i = 0; i < cnt; i++) if (!merged[i]) emit_prime(lvl[i].val, lvl[i].care);
    /* dedupe nxt */
    htsz = 1; while (htsz < 4 * (ncnt + 1)) htsz <<= 1;
    memset(ht, 0, sizeof(uint64_t) * htsz);
    int m = 0;
    for (int i = 0; i < ncnt; i++) {
      uint64_t key = ((uint64_t)nxt[i].care << 32) | nxt[i].val;
      int r = ht_find(key);
      if (r < 0) { ht[-1 - r] = key + 1; lvl[m++] = nxt[i]; }
    }
    cnt = m;
  }
}

static void handle_kset(void) {
  /* free pairs inside S */
  nfp = 0;
  for (int i = 0; i < k; i++) for (int j = i + 1; j < k; j++) {
    int u = S[i], v = S[j];
    if (fx[u][v] == 0) { fpu[nfp] = u < v ? u : v; fpv[nfp] = u < v ? v : u; nfp++; }
  }
  npts = 0;
  ext_rec(0, (1u << k) - 1);
  if (npts == 0) { n_ksets_zero++; return; }
  if (npts <= limit) {
    n_ksets_direct++;
    qm();
    return;
  }
  n_ksets_tri++;
  /* 3-cycle clause; collect literals first (cyc_lit may emit definitions) */
  int lits[64], nl = 0, sat = 0;
  for (int a = 0; a < k; a++) for (int b = a + 1; b < k; b++) for (int c = b + 1; c < k; c++) {
    int l = cyc_lit(S[a], S[b], S[c]);
    if (l == TRUE_LIT) sat = 1;
    else if (l != FALSE_LIT) lits[nl++] = l;
  }
  if (sat) return;
  cls_begin();
  for (int i = 0; i < nl; i++) cls_add(lits[i]);
  if (cls_end()) ncls_tri++;
}

/* fixed 3-cycle among {x} U S[0..d-1] containing x */
static int closes_fixed_cycle(int d, int x) {
  for (int i = 0; i < d; i++) for (int j = i + 1; j < d; j++) {
    int a = S[i], b = S[j];
    if (fx[a][b] == 0 || fx[b][x] == 0 || fx[x][a] == 0) continue;
    if (fx[a][b] == 1 && fx[b][x] == 1 && fx[x][a] == 1) return 1;
    if (fx[a][b] == -1 && fx[b][x] == -1 && fx[x][a] == -1) return 1;
  }
  return 0;
}

static void comb_rec(int d, int start) {
  if (d == k) { handle_kset(); return; }
  for (int x = start; x <= n - (k - d); x++) {
    if (closes_fixed_cycle(d, x)) { n_ksets_skip_cyc++; continue; }
    S[d] = x;
    comb_rec(d + 1, x + 1);
  }
}

int main(int argc, char **argv) {
  if (argc < 5) {
    fprintf(stderr, "usage: encode MATRIX k limit OUT.cnf [MAP.txt] [--count]\n");
    return 1;
  }
  const char *mfile = argv[1];
  k = atoi(argv[2]); limit = atoi(argv[3]);
  const char *out = argv[4];
  const char *mapname = NULL;
  for (int i = 5; i < argc; i++) {
    if (!strcmp(argv[i], "--count")) count_only = 1; else mapname = argv[i];
  }
  if (limit > 5900) limit = 5900;
  FILE *in = fopen(mfile, "r");
  if (!in) { perror(mfile); return 1; }
  /* read tokens */
  char tok[16]; int cells = 0; static char cellv[MAXN * MAXN];
  while (fscanf(in, "%15s", tok) == 1) {
    if (cells >= MAXN * MAXN) { fprintf(stderr, "too big\n"); return 1; }
    cellv[cells++] = tok[0];
  }
  fclose(in);
  n = 0; while (n * n < cells) n++;
  if (n * n != cells || n > MAXN) { fprintf(stderr, "not square: %d cells\n", cells); return 1; }
  for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) {
    char c = cellv[i * n + j];
    if (c == '1') { fx[i][j] = 1; fx[j][i] = -1; }
    else if (c == '0') { fx[i][j] = -1; fx[j][i] = 1; }
    else if (c == '*') { fx[i][j] = fx[j][i] = 0; }
    else { fprintf(stderr, "bad cell %c\n", c); return 1; }
  }
  tvar = calloc((size_t)MAXN * MAXN * MAXN, sizeof(int));
  lvl = malloc(sizeof(cube_t) * 6000 * 64);
  nxt = malloc(sizeof(cube_t) * 6000 * 64);
  merged = malloc(6000 * 64);
  ht = malloc(sizeof(uint64_t) * (1 << 22));
  if (mapname && !count_only) mapf = fopen(mapname, "w");
  nvars = 0;
  for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++)
    if (fx[i][j] == 0) {
      avar[i][j] = ++nvars;
      if (mapf) fprintf(mapf, "%d a %d %d\n", nvars, i, j);
    }
  int narc = nvars;
  char tmpname[4096];
  snprintf(tmpname, sizeof tmpname, "%s.body", out);
  if (!count_only) { body = fopen(tmpname, "w"); if (!body) { perror(tmpname); return 1; } }
  comb_rec(0, 0);
  fprintf(stderr,
          "c n=%d k=%d limit=%d arcvars=%d totalvars=%d clauses=%lld literals=%lld\n"
          "c ksets: direct=%lld tri=%lld zero-orderings=%lld prunes-by-fixed-cycle=%lld\n"
          "c clauses: direct=%lld tri=%lld tdef=%lld\n",
          n, k, limit, narc, nvars, ncls, nlits, n_ksets_direct, n_ksets_tri, n_ksets_zero,
          n_ksets_skip_cyc, ncls_direct, ncls_tri, ncls_tdef);
  if (count_only) return 0;
  fclose(body);
  FILE *o = fopen(out, "w");
  fprintf(o, "p cnf %d %lld\n", nvars, ncls);
  FILE *b = fopen(tmpname, "r");
  static char buf[1 << 20]; size_t r;
  while ((r = fread(buf, 1, sizeof buf, b)) > 0) fwrite(buf, 1, r, o);
  fclose(b); fclose(o); remove(tmpname);
  if (mapf) fclose(mapf);
  return 0;
}
