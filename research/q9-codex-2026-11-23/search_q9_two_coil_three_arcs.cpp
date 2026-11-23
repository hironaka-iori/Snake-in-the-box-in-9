// A path consists of a first arc of C, an arc of an isometric image D,
// and a disjoint final arc of C. Each switch is a single Q9 edge.
// Usage: target, mode (control/local/three_cycle/random), placement count, RNG
// seed, optional minimum vertex count for each of the three arcs (default 3).
// Standard input contains the 192 ordered cycle vertices.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <random>
#include <string>
#include <vector>
using namespace std;
const int N = 192;
int cycleV[N], imageV[N], indexC[512], required;
long long placements = 0, middles = 0, eligible = 0, intervals = 0;
int wrap(int x) { return x >= N ? x - N : x < 0 ? x + N : x; }
bool near(int x, int y) { return popcount(unsigned(x ^ y)) == 1; }
bool verify(const vector<int> &p, bool cycle = false) {
  for (int i = 0; i < p.size(); i++)
    for (int j = 0; j < i; j++) {
      if (p[i] == p[j] ||
          near(p[i], p[j]) !=
              (j + 1 == i || (cycle && j == 0 && i + 1 == p.size())))
        return false;
    }
  return true;
}
int minArm = 3;
bool test() {
  ++placements;
  array<vector<int>, N> conflicts, neighbors;
  for (int z = 0; z < N; ++z) {
    int x = imageV[z], same = indexC[x];
    if (same >= 0)
      conflicts[z].push_back(same);
    for (int bit = 0; bit < 9; ++bit) {
      int i = indexC[x ^ (1 << bit)];
      if (i >= 0) {
        conflicts[z].push_back(i);
        neighbors[z].push_back(i);
      }
    }
  }

  for (int start = 0; start < N; ++start) {
    array<int, N> hits{};
    int clear = N;
    for (int len = 1; len < N; ++len) {
      int end = wrap(start + len - 1);
      for (int i : conflicts[end])
        if (!hits[i]++)
          --clear;
      bool live = false;
      for (int i : neighbors[start])
        if (hits[i] == 1) {
          live = true;
          break;
        }
      if (!live)
        break;
      if (len < minArm)
        continue;
      ++middles;
      int arms = required + 1 - len;
      if (arms < 2 * minArm || clear + 2 < arms)
        continue;
      for (int i : neighbors[start])
        if (hits[i] == 1)
          for (int j : neighbors[end])
            if (hits[j] == 1 && i != j && wrap(i - j) != 1 &&
                wrap(j - i) != 1) {
              ++eligible;
              for (int di : {-1, 1}) {
                int left = 1, xi = i;
                while (!hits[wrap(xi + di)]) {
                  xi = wrap(xi + di);
                  ++left;
                }
                if (left < minArm)
                  continue;
                for (int dj : {-1, 1}) {
                  int right = 1, xj = j;
                  while (!hits[wrap(xj + dj)]) {
                    xj = wrap(xj + dj);
                    ++right;
                  }
                  for (int a = max(minArm, arms - right);
                       a <= min(left, arms - minArm); ++a) {
                    ++intervals;
                    int b = arms - a;
                    int lo = di > 0 ? i : wrap(i - a + 1),
                        ro = dj > 0 ? j : wrap(j - b + 1);
                    if (wrap(ro - lo) <= a || wrap(lo - ro) <= b)
                      continue;
                    vector<int> p;
                    for (int k = a - 1; k >= 0; --k)
                      p.push_back(cycleV[wrap(i + k * di)]);
                    for (int k = 0; k < len; ++k)
                      p.push_back(imageV[wrap(start + k)]);
                    for (int k = 0; k < b; ++k)
                      p.push_back(cycleV[wrap(j + k * dj)]);
                    if (p.size() != required + 1 || !verify(p))
                      exit(6);
                    cout << "FOUND " << placements << " " << a << " " << len
                         << " " << b;
                    for (int v : p)
                      cout << " " << v;
                    cout << endl;
                    return true;
                  }
                }
              }
            }
    }
  }
  return false;
}
int main(int argc, char **argv) {
  if (argc != 5 && argc != 6)
    return 2;
  required = stoi(argv[1]);
  string mode = argv[2];
  if (argc == 6)
    minArm = stoi(argv[5]);
  if (minArm < 1)
    return 2;
  int count = stoi(argv[3]);
  mt19937 rng(stoul(argv[4]));
  fill(indexC, indexC + 512, -1);
  vector<int> base;
  for (int i = 0; i < N; ++i) {
    if (!(cin >> cycleV[i]) || cycleV[i] < 0 || cycleV[i] >= 512)
      return 3;
    indexC[cycleV[i]] = i;
    base.push_back(cycleV[i]);
  }
  if (!verify(base, true))
    return 4;
  array<int, 9> id;
  iota(id.begin(), id.end(), 0);
  vector<array<int, 9>> perms{id};
  for (int i = 0; i < 9; ++i)
    for (int j = 0; j < i; ++j) {
      auto p = id;
      swap(p[i], p[j]);
      perms.push_back(p);
    }
  if (mode == "three_cycle") {
    perms.clear();
    for (int i = 0; i < 9; ++i)
      for (int j = 0; j < i; ++j)
        for (int k = 0; k < j; ++k) {
          auto p = id;
          p[i] = j;
          p[j] = k;
          p[k] = i;
          perms.push_back(p);
          p[i] = k;
          p[k] = j;
          p[j] = i;
          perms.push_back(p);
        }
  }
  if (mode != "control" && mode != "local" && mode != "random" &&
      mode != "three_cycle")
    return 2;
  for (int t = 0; t < count; ++t) {
    auto p = id;
    int shift = 0;
    if (mode == "local" || mode == "three_cycle") {
      if (t >= 512 * int(perms.size()))
        break;
      p = perms[t / 512];
      shift = t % 512;
    }
    if (mode == "random") {
      shuffle(p.begin(), p.end(), rng);
      shift = rng() % 512;
    }
    int mapping[512]{};
    for (int x = 1; x < 512; ++x)
      mapping[x] = mapping[x & (x - 1)] | (1 << p[countr_zero(unsigned(x))]);
    for (int i = 0; i < N; ++i)
      imageV[i] = mapping[cycleV[i]] ^ shift;
    if (test())
      return 0;
  }
  cout << "NO_JOIN placements " << placements
       << " middle_arcs_passing_first_attachment " << middles
       << " eligible_endpoint_pairs " << eligible << " interval_checks "
       << intervals << endl;
}
