// pivenum.cpp -- pivot AllSAT enumerator for TT_k-free tournaments, plus helpers.
//
// Every TT_k-free tournament T on n vertices has a vertex w of maximum
// out-degree d >= ceil((n-1)/2); A = In(w) and B = Out(w) are TT_{k-1}-free.
// So T is a completion of a pivot instance  A -w- B  (arcs inside A and B
// fixed, A -> w -> B, all A x B arcs free) for some A, B from complete
// catalogues of TT_{k-1}-free tournaments on n-1-d and d vertices.  With
// --maxdeg every vertex is also required to have out-degree <= d (valid,
// since w has maximum out-degree), which prunes duplicates.
//
// Modes (all read/write digraph6 '&' strings, adjacency bit (i,j) = i->j):
//   pivenum enum K CAT_A CAT_B [--maxdeg] [--time SEC] [--maxmodels M]
//       jobs "ia ib" (0-based catalogue lines) on stdin; for each job prints
//       "R ia ib arcvars clauses status models seconds" and one "T <d6>" per
//       model (labelled; every model is checked to be TT_K-free and, with
//       --maxdeg, to respect the degree bound).  status: complete|timeout|maxmodels
//   pivenum filter K           stdin d6 -> stdout the TT_K-free ones
//   pivenum extend K           stdin d6 (n vertices) -> stdout every TT_K-free
//                              one-vertex extension (n+1 vertices, labelled)
//   pivenum dumpcnf K CAT_A CAT_B ia ib [--maxdeg]   DIMACS of one job
//
// Build: c++ -O2 -std=c++17 -o build/pivenum src/pivenum.cpp -I<cadical include> <libcadical.a>

#include <cadical.hpp>

#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>

#include "ttenc.h"

using namespace std;
typedef uint64_t mask;

static vector<mask> from_d6(const string &s) {
  if (s.size() < 2 || s[0] != '&') { fprintf(stderr, "bad d6: %s\n", s.c_str()); exit(1); }
  int n = s[1] - 63;
  vector<mask> out(n, 0);
  int bit = 0;
  for (size_t c = 2; c < s.size(); c++) {
    int v = s[c] - 63;
    for (int t = 5; t >= 0; t--, bit++) {
      if (bit >= n * n) break;
      if ((v >> t) & 1) out[bit / n] |= (mask)1 << (bit % n);
    }
  }
  return out;
}

static string to_d6(const vector<mask> &out) {
  int n = out.size();
  string s = "&";
  s += (char)(n + 63);
  int acc = 0, nb = 0;
  for (int i = 0; i < n; i++)
    for (int j = 0; j < n; j++) {
      acc = (acc << 1) | (int)((out[i] >> j) & 1);
      if (++nb == 6) { s += (char)(acc + 63); acc = 0; nb = 0; }
    }
  if (nb) { acc <<= (6 - nb); s += (char)(acc + 63); }
  return s;
}

static bool tt_rec(const vector<mask> &out, mask cand, int need) {
  if (need == 0) return true;
  if (__builtin_popcountll(cand) < need) return false;
  mask c = cand;
  while (c) {
    int v = __builtin_ctzll(c);
    c &= c - 1;
    if (tt_rec(out, cand & out[v], need - 1)) return true;
  }
  return false;
}
static bool has_tt(const vector<mask> &out, int k) {
  int n = out.size();
  mask all = (n == 64) ? ~(mask)0 : (((mask)1 << n) - 1);
  return tt_rec(out, all, k);
}

static vector<vector<mask>> read_cat(const char *path) {
  ifstream f(path);
  if (!f) { fprintf(stderr, "cannot open %s\n", path); exit(1); }
  vector<vector<mask>> v;
  string line;
  while (getline(f, line)) {
    while (!line.empty() && (line.back() == '\n' || line.back() == '\r' || line.back() == ' ')) line.pop_back();
    if (!line.empty()) v.push_back(from_d6(line));
  }
  return v;
}

// ---------------------------------------------------------------- CNF sink
struct Sink {
  vector<vector<int>> cls;
};
static void sink_emit(const int *lits, int len, void *ctx) {
  ((Sink *)ctx)->cls.emplace_back(lits, lits + len);
}

// at most K of lits true (Sinz sequential counter); returns next free var
static int atmost(vector<vector<int>> &cls, const vector<int> &l, int K, int nextvar) {
  int m = l.size();
  if (K >= m) return nextvar;
  if (K < 0) { cls.push_back({}); return nextvar; }
  if (K == 0) { for (int x : l) cls.push_back({-x}); return nextvar; }
  // s[i][j], i in 0..m-2, j in 0..K-1
  vector<vector<int>> s(m - 1, vector<int>(K));
  for (int i = 0; i < m - 1; i++) for (int j = 0; j < K; j++) s[i][j] = nextvar++;
  cls.push_back({-l[0], s[0][0]});
  for (int j = 1; j < K; j++) cls.push_back({-s[0][j]});
  for (int i = 1; i < m - 1; i++) {
    cls.push_back({-l[i], s[i][0]});
    cls.push_back({-s[i - 1][0], s[i][0]});
    for (int j = 1; j < K; j++) {
      cls.push_back({-l[i], -s[i - 1][j - 1], s[i][j]});
      cls.push_back({-s[i - 1][j], s[i][j]});
    }
    cls.push_back({-l[i], -s[i - 1][K - 1]});
  }
  cls.push_back({-l[m - 1], -s[m - 2][K - 1]});
  return nextvar;
}

struct Inst {
  int n = 0, a = 0, b = 0, narcs = 0, nvars = 0;
  vector<int> fixed;           // n*n
  vector<pair<int, int>> arcs;  // var -> (i,j), i<j, index var-1
  vector<vector<int>> cls;
};

static int g_limit = 5900;
static const char *g_config = nullptr;
static Inst build(const vector<mask> &A, const vector<mask> &B, int k, bool maxdeg, int mindeg = -1) {
  Inst I;
  I.a = A.size(); I.b = B.size(); I.n = I.a + 1 + I.b;
  int n = I.n, a = I.a, w = a;
  I.fixed.assign(n * n, 0);
  auto set = [&](int u, int v) {  // u -> v
    if (u < v) I.fixed[u * n + v] = 1; else I.fixed[v * n + u] = -1;
  };
  for (int i = 0; i < a; i++) for (int j = 0; j < a; j++) if (i != j && ((A[i] >> j) & 1)) set(i, j);
  for (int i = 0; i < a; i++) set(i, w);
  for (int j = 0; j < I.b; j++) set(w, a + 1 + j);
  for (int i = 0; i < I.b; i++) for (int j = 0; j < I.b; j++)
    if (i != j && ((B[i] >> j) & 1)) set(a + 1 + i, a + 1 + j);
  Sink sk;
  tte_init(n, k, g_limit, I.fixed.data(), sink_emit, &sk);
  for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++)
    if (I.fixed[i * n + j] == 0) I.arcs.push_back({i, j});
  I.narcs = I.arcs.size();
  tte_run();
  I.nvars = tte_nvars();
  I.cls.swap(sk.cls);
  if (maxdeg) {
    int d = I.b, next = I.nvars + 1;
    for (int x = 0; x < a; x++) {
      vector<int> l;
      for (int y = a + 1; y < n; y++) l.push_back(tte_avar[x][y]);  // x -> y
      int K = d - 1 - __builtin_popcountll(A[x]);
      next = atmost(I.cls, l, K, next);
    }
    for (int yi = 0; yi < I.b; yi++) {
      int y = a + 1 + yi;
      vector<int> l;
      for (int x = 0; x < a; x++) l.push_back(-tte_avar[x][y]);  // y -> x
      int K = d - __builtin_popcountll(B[yi]);
      next = atmost(I.cls, l, K, next);
    }
    I.nvars = next - 1;
  }
  if (mindeg >= 0) {  // every out-degree >= mindeg (valid when in-neighbourhoods are TT_{k-1}-free: in-degree <= R(k-1)-1)
    int next = I.nvars + 1;
    for (int x = 0; x < a; x++) {
      vector<int> l;
      for (int y = a + 1; y < n; y++) l.push_back(-tte_avar[x][y]);  // y -> x (x loses)
      int need = mindeg - 1 - __builtin_popcountll(A[x]);            // wins needed against B
      next = atmost(I.cls, l, I.b - need, next);
    }
    for (int yi = 0; yi < I.b; yi++) {
      int y = a + 1 + yi;
      vector<int> l;
      for (int x = 0; x < a; x++) l.push_back(tte_avar[x][y]);  // x -> y (y loses)
      int need = mindeg - __builtin_popcountll(B[yi]);
      next = atmost(I.cls, l, a - need, next);
    }
    I.nvars = next - 1;
  }
  return I;
}

static vector<mask> complete(const Inst &I, const vector<char> &val) {
  int n = I.n;
  vector<mask> out(n, 0);
  for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) {
    int f = I.fixed[i * n + j];
    if (f == 1) out[i] |= (mask)1 << j;
    else if (f == -1) out[j] |= (mask)1 << i;
  }
  for (int v = 0; v < I.narcs; v++) {
    auto [i, j] = I.arcs[v];
    if (val[v]) out[i] |= (mask)1 << j; else out[j] |= (mask)1 << i;
  }
  return out;
}

struct Clock : CaDiCaL::Terminator {
  chrono::steady_clock::time_point t0;
  double limit;
  bool terminate() override {
    return limit > 0 && chrono::duration<double>(chrono::steady_clock::now() - t0).count() > limit;
  }
};

static int mode_enum(int argc, char **argv) {
  int k = atoi(argv[2]);
  auto CA = read_cat(argv[3]);
  auto CB = read_cat(argv[4]);
  bool maxdeg = false;
  int mindeg = -1;
  double tlim = 0;
  long maxmodels = 10000000;
  for (int i = 5; i < argc; i++) {
    if (!strcmp(argv[i], "--maxdeg")) maxdeg = true;
    else if (!strcmp(argv[i], "--time")) tlim = atof(argv[++i]);
    else if (!strcmp(argv[i], "--maxmodels")) maxmodels = atol(argv[++i]);
    else if (!strcmp(argv[i], "--mindeg")) mindeg = atoi(argv[++i]);
    else if (!strcmp(argv[i], "--limit")) g_limit = atoi(argv[++i]);
    else if (!strcmp(argv[i], "--config")) g_config = argv[++i];
  }
  int ia, ib;
  while (scanf("%d %d", &ia, &ib) == 2) {
    auto t0 = chrono::steady_clock::now();
    Inst I = build(CA.at(ia), CB.at(ib), k, maxdeg, mindeg);
    CaDiCaL::Solver S;
    if (g_config) S.configure(g_config);
    Clock clk; clk.t0 = t0; clk.limit = tlim;
    S.connect_terminator(&clk);
    bool empty = false;
    for (auto &c : I.cls) {
      if (c.empty()) empty = true;
      for (int l : c) S.add(l);
      S.add(0);
    }
    long models = 0;
    string status = "complete";
    vector<string> lines;
    while (!empty) {
      int r = S.solve();
      if (r == 20) break;
      if (r != 10) { status = "timeout"; break; }
      vector<char> val(I.narcs);
      for (int v = 1; v <= I.narcs; v++) val[v - 1] = S.val(v) > 0;
      auto T = complete(I, val);
      if (has_tt(T, k)) { fprintf(stderr, "BUG: model contains TT%d\n", k); return 3; }
      for (int x = 0; x < I.n; x++) {
        int od = __builtin_popcountll(T[x]);
        if ((maxdeg && od > I.b) || (mindeg >= 0 && od < mindeg)) { fprintf(stderr, "BUG: degree bound violated\n"); return 3; }
      }
      lines.push_back(to_d6(T));
      models++;
      if (models >= maxmodels) { status = "maxmodels"; break; }
      for (int v = 1; v <= I.narcs; v++) S.add(val[v - 1] ? -v : v);  // block this arc assignment
      S.add(0);
    }
    double secs = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
    printf("R %d %d %d %zu %s %ld %.3f\n", ia, ib, I.narcs, I.cls.size(), status.c_str(), models, secs);
    for (auto &s : lines) printf("T %s\n", s.c_str());
    fflush(stdout);
  }
  return 0;
}

static int mode_filter(int argc, char **argv) {
  int k = atoi(argv[2]);
  string line;
  while (getline(cin, line)) {
    if (line.empty()) continue;
    if (!has_tt(from_d6(line), k)) cout << line << "\n";
  }
  return 0;
}

static int mode_extend(int argc, char **argv) {
  int k = atoi(argv[2]);
  string line;
  while (getline(cin, line)) {
    if (line.empty()) continue;
    auto T = from_d6(line);
    int n = T.size();
    for (mask outset = 0; outset < ((mask)1 << n); outset++) {  // new vertex n beats outset
      vector<mask> U(n + 1, 0);
      for (int i = 0; i < n; i++) {
        U[i] = T[i];
        if (!((outset >> i) & 1)) U[i] |= (mask)1 << n;
      }
      U[n] = outset;
      // TT_k through the new vertex: TT_{k-1} in its in-set or out-set would do it,
      // but full check is simple and exact:
      if (!has_tt(U, k)) cout << to_d6(U) << "\n";
    }
  }
  return 0;
}

static int mode_dump(int argc, char **argv) {
  int k = atoi(argv[2]);
  auto CA = read_cat(argv[3]);
  auto CB = read_cat(argv[4]);
  int ia = atoi(argv[5]), ib = atoi(argv[6]);
  bool maxdeg = false; int mindeg = -1;
  for (int i = 7; i < argc; i++) {
    if (!strcmp(argv[i], "--maxdeg")) maxdeg = true;
    else if (!strcmp(argv[i], "--mindeg")) mindeg = atoi(argv[++i]);
  }
  Inst I = build(CA.at(ia), CB.at(ib), k, maxdeg, mindeg);
  printf("p cnf %d %zu\n", I.nvars, I.cls.size());
  for (auto &c : I.cls) { for (int l : c) printf("%d ", l); printf("0\n"); }
  return 0;
}

int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: see header of src/pivenum.cpp\n"); return 1; }
  string m = argv[1];
  if (m == "enum" && argc >= 5) return mode_enum(argc, argv);
  if (m == "filter") return mode_filter(argc, argv);
  if (m == "extend") return mode_extend(argc, argv);
  if (m == "dumpcnf" && argc >= 7) return mode_dump(argc, argv);
  fprintf(stderr, "bad mode\n");
  return 1;
}
