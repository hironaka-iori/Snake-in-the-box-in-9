#include <algorithm>
#include <array>
#include <bit>
#include <iostream>
#include <numeric>
#include <random>
#include <vector>
using namespace std;
constexpr int N = 192;
using Mask = array<uint64_t, 8>;
using Cycle = array<int, N>;
struct Masks {
  Mask occ{}, closed{};
};
int mod(int x) { return x < 0 ? x + N : x >= N ? x - N : x; }
int distance9(int x, int y) { return popcount(unsigned(x ^ y)); }
bool verify(const vector<int> &p, bool circle = false) {
  for (int i = 0; i < p.size(); i++)
    for (int j = 0; j < i; j++)
      if (p[i] == p[j] ||
          ((distance9(p[i], p[j]) == 1) !=
           (j + 1 == i || (circle && j == 0 && i + 1 == p.size()))))
        return false;
  return true;
}
struct Table {
  array<array<Masks, N>, 8> seg;
  void build(const Cycle &p) {
    for (int i = 0; i < N; i++) {
      auto &v = seg[0][i];
      v = {};
      int u = p[i];
      v.occ[u / 64] |= 1ull << (u % 64);
      v.closed = v.occ;
      for (int d = 0; d < 9; d++) {
        int w = u ^ (1 << d);
        v.closed[w / 64] |= 1ull << (w % 64);
      }
    }
    for (int k = 1; k < bit_width(unsigned(N)); k++)
      for (int i = 0; i < N; i++) {
        auto &v = seg[k][i];
        const auto &a = seg[k - 1][i];
        const auto &b = seg[k - 1][mod(i + (1 << (k - 1)))];
        for (int g = 0; g < 8; g++) {
          v.occ[g] = a.occ[g] | b.occ[g];
          v.closed[g] = a.closed[g] | b.closed[g];
        }
      }
  }
  Masks read(int start, int dir, int n) const {
    int i = dir == 1 ? start : mod(start - n + 1),
        k = bit_width(unsigned(n)) - 1;
    const auto &a = seg[k][i];
    const auto &b = seg[k][mod(i + n - (1 << k))];
    Masks r;
    for (int g = 0; g < 8; g++) {
      r.occ[g] = a.occ[g] | b.occ[g];
      r.closed[g] = a.closed[g] | b.closed[g];
    }
    return r;
  }
};
struct Half {
  int i, j, ci, dj, a, b;
  Mask words;
};
Cycle C, D;
Table ct, dt;
array<int, 512> ix;
array<vector<int>, N> contact, neighbor;
long long placements = 0, lc = 0, rc = 0, pairsSeen = 0, checks = 0;
int target, half, minArc;
bool exclusive_control = false;
array<vector<Half>, N> leftByDEnd, rightByCStart;
void halves(int total, bool left) {
  for (int j = 0; j < N; j++)
    for (int i : neighbor[j]) {
      for (int dj : {-1, 1}) {
        int plus = N, minus = N;
        for (int b = 1; b <= total - minArc; b++) {
          int q = mod(j + dj * (b - 1));
          bool stop = false;
          for (int h : contact[q]) {
            if (h == i) {
              if (b != 1)
                stop = true;
              continue;
            }
            plus = min(plus, mod(h - i));
            minus = min(minus, mod(i - h));
          }
          if (stop)
            break;
          int a = total - b;
          if (b < minArc || a >= N || b >= N)
            continue;
          for (int ci : {-1, 1}) {
            if (a > (ci > 0 ? plus : minus))
              continue;
            int start = mod(i + ci * (a - 1));
            Half h{i, j, ci, dj, a, b, {}};
            auto one = ct.read(i, ci, a), two = dt.read(j, dj, b);
            for (int g = 0; g < 8; g++)
              h.words[g] = left ? (one.closed[g] | two.closed[g])
                                : (one.occ[g] | two.occ[g]);
            if (left) {
              leftByDEnd[q].push_back(h);
              lc++;
            } else {
              rightByCStart[start].push_back(h);
              rc++;
            }
          }
        }
      }
    }
}
void append(vector<int> &p, const Half &h) {
  for (int k = h.a - 1; k >= 0; --k)
    p.push_back(C[mod(h.i + k * h.ci)]);
  for (int k = 0; k < h.b; ++k)
    p.push_back(D[mod(h.j + k * h.dj)]);
}
bool search() {
  placements++;
  for (int j = 0; j < N; j++) {
    contact[j].clear();
    neighbor[j].clear();
    leftByDEnd[j].clear();
    rightByCStart[j].clear();
    int x = D[j];
    if (ix[x] >= 0)
      contact[j].push_back(ix[x]);
    for (int d = 0; d < 9; d++) {
      int i = ix[x ^ (1 << d)];
      if (i >= 0) {
        contact[j].push_back(i);
        neighbor[j].push_back(i);
      }
    }
  }
  array<bool, 512> inD{};
  for (int v : D)
    inD[v] = true;
  dt.build(D);
  halves(half, true);
  halves(target + 1 - half, false);
  for (int q = 0; q < N; q++)
    for (int s : neighbor[q]) {
      int tip = C[s], g0 = tip / 64;
      uint64_t bit = 1ull << (tip % 64);
      for (const Half &l : leftByDEnd[q])
        for (const Half &r : rightByCStart[s]) {
          ++pairsSeen;
          bool ok = true;
          for (int g = 0; g < 8; g++)
            if ((l.words[g] & r.words[g]) != (g == g0 ? bit : 0)) {
              ok = false;
              break;
            }
          if (!ok)
            continue;
          ++checks;
          vector<int> p;
          append(p, l);
          append(p, r);
          if (exclusive_control) {
            int offset = 0;
            bool pass = true;
            int axis = 0;
            for (int n : {l.a, l.b, r.a, r.b}) {
              bool hit = false;
              for (int m = 0; m < n; m++) {
                int v = p[offset + m];
                hit |= (axis % 2 == 0 ? !inD[v] : ix[v] < 0);
              }
              pass &= hit;
              offset += n;
              ++axis;
            }
            if (!pass)
              continue;
          }
          if (!verify(p))
            continue;
          cout << "FOUND " << placements << " " << l.a << " " << l.b << " "
               << r.a << " " << r.b;
          for (int v : p)
            cout << " " << v;
          cout << endl;
          return true;
        }
    }
  return false;
}
int main(int argc, char **argv) {
  exclusive_control = argc == 8 && string(argv[7]) == "--exclusive";
  if (argc != 7 && !exclusive_control)
    return 1;
  target = stoi(argv[1]);
  int halfArg = stoi(argv[2]);
  half = halfArg;
  minArc = stoi(argv[3]);
  string mode = argv[4];
  int count = stoi(argv[5]);
  mt19937 rng(stoul(argv[6]));
  if (minArc < 1 ||
      (halfArg != 0 && (half >= N || target + 1 - half >= N ||
                        half < 2 * minArc || target + 1 - half < 2 * minArc)))
    return 2;
  ix.fill(-1);
  for (int i = 0; i < N; i++) {
    if (!(cin >> C[i]) || C[i] < 0 || C[i] > 511)
      return 3;
    ix[C[i]] = i;
  }
  if (!verify(vector<int>(C.begin(), C.end()), true))
    return 4;
  ct.build(C);
  array<int, 9> id;
  iota(id.begin(), id.end(), 0);
  vector<array<int, 9>> perms{id};
  for (int i = 0; i < 9; i++)
    for (int j = 0; j < i; j++) {
      auto p = id;
      swap(p[i], p[j]);
      perms.push_back(p);
    }
  if (mode != "local" && mode != "random" && mode != "sparse" &&
      mode != "specific")
    return 5;
  for (int t = 0; t < (mode == "specific" ? 1 : count); t++) {
    auto p = id;
    int shift;
    if (mode == "specific") {
      if (count < 0 || count >= 512 * perms.size())
        return 5;
      p = perms[count / 512];
      shift = count % 512;
    } else if (mode == "random") {
      shuffle(p.begin(), p.end(), rng);
      shift = rng() % 512;
    } else if (mode == "sparse") {
      p = perms[t % perms.size()];
      shift = (t / perms.size()) % 512;
    } else {
      if (t >= 512 * perms.size())
        break;
      p = perms[t / 512];
      shift = t % 512;
    }
    int m[512]{};
    for (int v = 1; v < 512; v++)
      m[v] = m[v & (v - 1)] | (1 << p[countr_zero(unsigned(v))]);
    for (int i = 0; i < N; i++)
      D[i] = m[C[i]] ^ shift;
    int startHalf = halfArg ? halfArg : max(2 * minArc, target + 2 - N),
        endHalf = halfArg ? halfArg : min(N - 1, target + 1 - 2 * minArc);
    for (half = startHalf; half <= endHalf; half++)
      if (search())
        return 0;
  }
  cout << "NO_JOIN placements " << placements << " left_halves " << lc
       << " right_halves " << rc << " adjacent_pairs " << pairsSeen
       << " pairwise_tests " << checks << endl;
}
