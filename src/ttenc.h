/*
 * ttenc.h -- the TT_k-exclusion encoder of encode.c as a reusable header
 * (C and C++), emitting clauses through a callback instead of a file.
 *
 * Same semantics as src/encode.c (see there): variables 1..F are the free
 * pairs i<j in row-major order (true iff i->j); 3-cycle variables are created
 * on demand after them.  Per k-set: skip if it contains a fixed 3-cycle;
 * enumerate orderings compatible with the fixed arcs (up to limit+1); <= limit
 * orderings -> prime implicants of the forbidden assignments (one clause
 * each); otherwise one 3-cycle clause.
 *
 * Usage: tte_init(n, k, limit, fixed, emit, ctx) where fixed[i][j] is +1
 * (i->j), -1 (j->i) or 0 (free); then tte_run().  tte_nvars() gives the
 * number of variables used so far (callers may allocate more after it).
 * Single-threaded (file-scope state).
 */
#ifndef TTENC_H
#define TTENC_H
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define TTE_MAXN 64
#define TTE_TRUE 0x7fffffff
#define TTE_FALSE (-0x7fffffff)

typedef void (*tte_emit_fn)(const int *lits, int len, void *ctx);

static int tte_n, tte_k, tte_limit;
static int tte_fx[TTE_MAXN][TTE_MAXN];
static int tte_avar[TTE_MAXN][TTE_MAXN];
static int tte_nv;
static int *tte_tvar;
static tte_emit_fn tte_emit;
static void *tte_ctx;
static long long tte_ncls;

static int tte_lit(int u, int v) {
  if (tte_fx[u][v] == 1) return TTE_TRUE;
  if (tte_fx[u][v] == -1) return TTE_FALSE;
  int a = u < v ? u : v, b = u < v ? v : u;
  return (u < v) ? tte_avar[a][b] : -tte_avar[a][b];
}

static int tte_buf[4096], tte_len, tte_sat;
static void tte_begin(void) { tte_len = 0; tte_sat = 0; }
static void tte_add(int l) {
  if (l == TTE_TRUE) { tte_sat = 1; return; }
  if (l == TTE_FALSE) return;
  for (int i = 0; i < tte_len; i++) {
    if (tte_buf[i] == l) return;
    if (tte_buf[i] == -l) { tte_sat = 1; return; }
  }
  tte_buf[tte_len++] = l;
}
static void tte_end(void) {
  if (tte_sat) return;
  tte_ncls++;
  tte_emit(tte_buf, tte_len, tte_ctx);
}

static int tte_cyc_lit(int a, int b, int c) {
  int t;
  if (a > b) { t = a; a = b; b = t; }
  if (b > c) { t = b; b = c; c = t; }
  if (a > b) { t = a; a = b; b = t; }
  int v[3] = {a, b, c};
  for (int i = 0; i < 3; i++) {
    int x = v[i], y = v[(i + 1) % 3], z = v[(i + 2) % 3];
    if (tte_fx[x][y] == 1 && tte_fx[x][z] == 1) return TTE_FALSE;
    if (tte_fx[x][y] == -1 && tte_fx[x][z] == -1) return TTE_FALSE;
  }
  int nfree = (tte_fx[a][b] == 0) + (tte_fx[a][c] == 0) + (tte_fx[b][c] == 0);
  if (nfree == 0) return TTE_TRUE;
  if (nfree == 1) {
    int x = -1, z = -1;
    for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) for (int l = 0; l < 3; l++) {
      if (i == j || j == l || i == l) continue;
      if (tte_fx[v[i]][v[j]] == 1 && tte_fx[v[j]][v[l]] == 1) { x = v[i]; z = v[l]; }
    }
    if (x < 0) { fprintf(stderr, "ttenc: internal path error\n"); exit(2); }
    return tte_lit(z, x);
  }
  long id = (long)a * TTE_MAXN * TTE_MAXN + (long)b * TTE_MAXN + c;
  if (tte_tvar[id]) return tte_tvar[id];
  int tv = ++tte_nv;
  tte_tvar[id] = tv;
  int cyc[2][3] = {{a, b, c}, {a, c, b}};
  for (int o = 0; o < 2; o++)
    for (int i = 0; i < 3; i++) {
      int x = cyc[o][i], y = cyc[o][(i + 1) % 3], z = cyc[o][(i + 2) % 3];
      tte_begin(); tte_add(-tv); tte_add(-tte_lit(x, y)); tte_add(tte_lit(y, z)); tte_end();
    }
  return tv;
}

static int tte_S[16], tte_ord[16];
static uint32_t tte_pts[6000];
static int tte_npts;
static int tte_fpu[64], tte_fpv[64], tte_nfp;

static void tte_ext_rec(int depth, uint32_t remaining) {
  if (tte_npts > tte_limit) return;
  if (depth == tte_k) {
    int pos[TTE_MAXN];
    for (int i = 0; i < tte_k; i++) pos[tte_ord[i]] = i;
    uint32_t p = 0;
    for (int b = 0; b < tte_nfp; b++) if (pos[tte_fpu[b]] < pos[tte_fpv[b]]) p |= 1u << b;
    tte_pts[tte_npts++] = p;
    return;
  }
  for (int i = 0; i < tte_k; i++) {
    if (!(remaining >> i & 1)) continue;
    int x = tte_S[i], ok = 1;
    for (int j = 0; j < tte_k && ok; j++)
      if (j != i && (remaining >> j & 1) && tte_fx[tte_S[j]][x] == 1) ok = 0;
    if (!ok) continue;
    tte_ord[depth] = x;
    tte_ext_rec(depth + 1, remaining & ~(1u << i));
    if (tte_npts > tte_limit) return;
  }
}

typedef struct { uint32_t val, care; } tte_cube_t;
static tte_cube_t *tte_lvl, *tte_nxt;
static char *tte_merged;
static uint64_t *tte_ht; static int tte_htsz;

static int tte_ht_find(uint64_t key) {
  uint64_t h = key * 0x9E3779B97F4A7C15ULL;
  int i = (int)(h >> 40) & (tte_htsz - 1);
  while (tte_ht[i]) { if (tte_ht[i] == key + 1) return i; i = (i + 1) & (tte_htsz - 1); }
  return -1 - i;
}

static void tte_emit_prime(uint32_t val, uint32_t care) {
  tte_begin();
  for (int b = 0; b < tte_nfp; b++) {
    if (!(care >> b & 1)) continue;
    int l = tte_lit(tte_fpu[b], tte_fpv[b]);
    tte_add((val >> b & 1) ? -l : l);
  }
  tte_end();
}

static void tte_qm(void) {
  int cnt = tte_npts;
  uint32_t full = (tte_nfp == 32) ? 0xffffffffu : ((1u << tte_nfp) - 1);
  for (int i = 0; i < cnt; i++) { tte_lvl[i].val = tte_pts[i]; tte_lvl[i].care = full; }
  while (cnt > 0) {
    tte_htsz = 1; while (tte_htsz < 4 * cnt) tte_htsz <<= 1;
    memset(tte_ht, 0, sizeof(uint64_t) * tte_htsz);
    for (int i = 0; i < cnt; i++) {
      uint64_t key = ((uint64_t)tte_lvl[i].care << 32) | tte_lvl[i].val;
      int r = tte_ht_find(key);
      if (r < 0) tte_ht[-1 - r] = key + 1;
      tte_merged[i] = 0;
    }
    int ncnt = 0;
    for (int i = 0; i < cnt; i++) {
      uint32_t care = tte_lvl[i].care, val = tte_lvl[i].val;
      for (int b = 0; b < tte_nfp; b++) {
        if (!(care >> b & 1)) continue;
        uint64_t key = ((uint64_t)care << 32) | (val ^ (1u << b));
        if (tte_ht_find(key) >= 0) {
          tte_merged[i] = 1;
          if (!(val >> b & 1)) {
            tte_nxt[ncnt].val = val & ~(1u << b);
            tte_nxt[ncnt].care = care & ~(1u << b);
            ncnt++;
          }
        }
      }
    }
    for (int i = 0; i < cnt; i++) if (!tte_merged[i]) tte_emit_prime(tte_lvl[i].val, tte_lvl[i].care);
    tte_htsz = 1; while (tte_htsz < 4 * (ncnt + 1)) tte_htsz <<= 1;
    memset(tte_ht, 0, sizeof(uint64_t) * tte_htsz);
    int m = 0;
    for (int i = 0; i < ncnt; i++) {
      uint64_t key = ((uint64_t)tte_nxt[i].care << 32) | tte_nxt[i].val;
      int r = tte_ht_find(key);
      if (r < 0) { tte_ht[-1 - r] = key + 1; tte_lvl[m++] = tte_nxt[i]; }
    }
    cnt = m;
  }
}

static void tte_handle_kset(void) {
  tte_nfp = 0;
  for (int i = 0; i < tte_k; i++) for (int j = i + 1; j < tte_k; j++) {
    int u = tte_S[i], v = tte_S[j];
    if (tte_fx[u][v] == 0) { tte_fpu[tte_nfp] = u < v ? u : v; tte_fpv[tte_nfp] = u < v ? v : u; tte_nfp++; }
  }
  tte_npts = 0;
  tte_ext_rec(0, (1u << tte_k) - 1);
  if (tte_npts == 0) return;
  if (tte_npts <= tte_limit) { tte_qm(); return; }
  int lits[64], nl = 0, sat = 0;
  for (int a = 0; a < tte_k; a++) for (int b = a + 1; b < tte_k; b++) for (int c = b + 1; c < tte_k; c++) {
    int l = tte_cyc_lit(tte_S[a], tte_S[b], tte_S[c]);
    if (l == TTE_TRUE) sat = 1;
    else if (l != TTE_FALSE) lits[nl++] = l;
  }
  if (sat) return;
  tte_begin();
  for (int i = 0; i < nl; i++) tte_add(lits[i]);
  tte_end();
}

static int tte_closes_fixed_cycle(int d, int x) {
  for (int i = 0; i < d; i++) for (int j = i + 1; j < d; j++) {
    int a = tte_S[i], b = tte_S[j];
    if (tte_fx[a][b] == 0 || tte_fx[b][x] == 0 || tte_fx[x][a] == 0) continue;
    if (tte_fx[a][b] == 1 && tte_fx[b][x] == 1 && tte_fx[x][a] == 1) return 1;
    if (tte_fx[a][b] == -1 && tte_fx[b][x] == -1 && tte_fx[x][a] == -1) return 1;
  }
  return 0;
}

static void tte_comb_rec(int d, int start) {
  if (d == tte_k) { tte_handle_kset(); return; }
  for (int x = start; x <= tte_n - (tte_k - d); x++) {
    if (tte_closes_fixed_cycle(d, x)) continue;
    tte_S[d] = x;
    tte_comb_rec(d + 1, x + 1);
  }
}

/* fixed: n x n, row-major, values +1/-1/0 (only i<j entries read) */
static void tte_init(int n, int k, int limit, const int *fixed, tte_emit_fn emit, void *ctx) {
  tte_n = n; tte_k = k; tte_limit = limit > 5900 ? 5900 : limit;
  tte_emit = emit; tte_ctx = ctx; tte_ncls = 0;
  if (!tte_tvar) {
    tte_tvar = (int *)calloc((size_t)TTE_MAXN * TTE_MAXN * TTE_MAXN, sizeof(int));
    tte_lvl = (tte_cube_t *)malloc(sizeof(tte_cube_t) * 6000 * 64);
    tte_nxt = (tte_cube_t *)malloc(sizeof(tte_cube_t) * 6000 * 64);
    tte_merged = (char *)malloc(6000 * 64);
    tte_ht = (uint64_t *)malloc(sizeof(uint64_t) * (1 << 22));
  } else {
    memset(tte_tvar, 0, sizeof(int) * (size_t)TTE_MAXN * TTE_MAXN * TTE_MAXN);
  }
  memset(tte_fx, 0, sizeof tte_fx);
  memset(tte_avar, 0, sizeof tte_avar);
  for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) {
    int f = fixed[i * n + j];
    tte_fx[i][j] = f; tte_fx[j][i] = -f;
  }
  tte_nv = 0;
  for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++)
    if (tte_fx[i][j] == 0) tte_avar[i][j] = ++tte_nv;
}

static int tte_narcs(void) {
  int c = 0;
  for (int i = 0; i < tte_n; i++) for (int j = i + 1; j < tte_n; j++) if (tte_fx[i][j] == 0) c++;
  return c;
}
static void tte_run(void) { tte_comb_rec(0, 0); }
static int tte_nvars(void) { return tte_nv; }

#endif
