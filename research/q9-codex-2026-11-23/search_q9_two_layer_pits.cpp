#include <algorithm>
#include <array>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <string>
#include <vector>
using namespace std;
array<int, 512> present, degree;
array<array<int, 3>, 512> neighbors;
int allowance;
long long nodes = 0;
int solve(vector<int> &verts, int goal) {
  if (--allowance < 0)
    return -1;
  ++nodes;
  array<bool, 512> seen{};
  vector<int> branch;
  for (int v : verts)
    if (present[v] && !seen[v]) {
      vector<int> c{v};
      seen[v] = true;
      int chosen = -1, bad = 0, end = -1;
      for (int z = 0; z < c.size(); z++) {
        int x = c[z], deg = 0;
        for (int k = 0; k < degree[x]; k++) {
          int w = neighbors[x][k];
          if (!present[w])
            continue;
          ++deg;
          if (!seen[w]) {
            seen[w] = true;
            c.push_back(w);
          }
        }
        if (deg <= 1)
          end = x;
        if (deg == 3) {
          bad++;
          chosen = x;
        }
      }
      if ((int)c.size() < goal)
        continue;
      if (!bad) {
        if (end < 0) {
          if (c.size() == goal)
            continue;
          int v0 = c[0];
          present[v0] = 0;
          for (int k = 0; k < degree[v0]; k++)
            if (present[neighbors[v0][k]])
              end = neighbors[v0][k];
        }
        int prev = -1;
        cout << "FOUND";
        while (end >= 0) {
          cout << " " << end;
          int next = -1;
          for (int k = 0; k < degree[end]; k++) {
            int w = neighbors[end][k];
            if (w != prev && present[w])
              next = w;
          }
          prev = end;
          end = next;
        }
        cout << endl;
        exit(0);
      }
      if (bad > 4 * ((int)c.size() - goal))
        continue;
      // At a degree-three vertex, at least one vertex of this closed
      // neighborhood must go.
      branch = {chosen};
      for (int k = 0; k < 3; k++)
        branch.push_back(neighbors[chosen][k]);
      for (int w : branch) {
        present[w] = 0;
        int res = solve(c, goal);
        present[w] = 1;
        if (res < 0)
          return -1;
      }
    }
  return 0;
}
int main(int argc, char **argv) {
  if (argc != 2)
    return 2;
  int goal = stoi(argv[1]) + 1;
  // Standard input: one Q8 induced linear forest per row: vertex count, then
  // its vertices.
  vector<vector<int>> pits;
  int n;
  while (cin >> n) {
    if (n < 1 || n > 256)
      return 3;
    vector<int> p(n);
    array<bool, 256> inside{};
    for (int &x : p) {
      if (!(cin >> x) || x < 0 || x > 255 || inside[x])
        return 3;
      inside[x] = true;
    }
    for (int x : p) {
      int d = 0;
      for (int k = 0; k < 8; k++)
        d += inside[x ^ (1 << k)];
      if (d > 2)
        return 4;
    }
    pits.push_back(p);
  }
  for (int i = 0; i < pits.size(); i++)
    for (int j = i; j < pits.size(); j++) {
      array<int, 8> pi;
      iota(pi.begin(), pi.end(), 0);
      long long survivors = 0, capped = 0;
      array<bool, 256> a{}, b{}, ia{}, ib{};
      for (int x : pits[i])
        a[x] = 1;
      for (int x : pits[j])
        b[x] = 1;
      for (int x = 0; x < 256; x++) {
        int k1 = 0, k2 = 0;
        for (int k = 0; k < 8; k++) {
          k1 += a[x ^ (1 << k)];
          k2 += b[x ^ (1 << k)];
        }
        ia[x] = a[x] && k1 == 2;
        ib[x] = b[x] && k2 == 2;
      }
      do {
        array<int, 256> ix{}, cost{};
        for (int x = 1; x < 256; x++)
          ix[x] = ix[x & (x - 1)] ^ (1 << pi[__builtin_ctz(x)]);
        for (int x : pits[i])
          for (int y : pits[j])
            cost[x ^ ix[y]] += ia[x] + ib[y];
        for (int t = 0; t < 256; t++) {
          if (cost[t] > 4 * ((int)pits[i].size() + (int)pits[j].size() - goal))
            continue;
          survivors++;
          vector<int> verts = pits[i];
          for (int y : pits[j])
            verts.push_back(256 + (ix[y] ^ t));
          present.fill(0);
          for (int v : verts)
            present[v] = 1;
          for (int v : verts) {
            degree[v] = 0;
            for (int axis = 0; axis < 9; axis++)
              if (present[v ^ (1 << axis)])
                neighbors[v][degree[v]++] = v ^ (1 << axis);
          }
          allowance = 20000;
          if (solve(verts, goal) < 0)
            capped++;
        }
      } while (next_permutation(pi.begin(), pi.end()));
      cout << i + 1 << " " << j + 1 << " screened-in " << survivors
           << " capped " << capped << " nodes cumulative " << nodes << endl;
    }
}
