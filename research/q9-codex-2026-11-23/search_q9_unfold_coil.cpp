// Independently place two directed arcs of the input coil around one shared
// vertex. Enumerate every relative coordinate permutation, pruning partial
// maps.
#define main original_q9_pivot_main
#include "search_q9_pivot.cpp"
#undef main
#include <set>
#include <string>

std::set<std::vector<int>> arcs(const std::vector<int> &coil, int length) {
  std::set<std::vector<int>> out;
  int n = coil.size();
  for (int root = 0; root < n; root++)
    for (int direction : {-1, 1}) {
      std::array<int, 9> label;
      label.fill(-1);
      int count = 0, pos = root;
      std::vector<int> arc{0};
      for (int step = 0; step < length; step++) {
        int j = (pos + n + direction) % n,
            axis = std::countr_zero(unsigned(coil[pos] ^ coil[j]));
        if (label[axis] < 0)
          label[axis] = count++;
        arc.push_back(arc.back() ^ (1 << label[axis]));
        pos = j;
      }
      if (!valid(arc))
        std::abort();
      out.insert(std::move(arc));
    }
  return out;
}
int main(int argc, char **argv) {
  if (argc != 3)
    return 2;
  int left = std::stoi(argv[1]), right = std::stoi(argv[2]);
  std::vector<int> coil;
  int x;
  while (std::cin >> x)
    coil.push_back(x);
  int n = coil.size();
  if (left < 1 || right < 1 || std::max(left, right) > n - 2)
    return 2;
  for (int i = 0; i < n; i++)
    for (int j = 0; j < i; j++) {
      int d = std::popcount(unsigned(coil[i] ^ coil[j]));
      if (!d || ((i == j + 1 || (j == 0 && i + 1 == n)) != (d == 1)))
        return 3;
    }
  auto a = arcs(coil, left), b = arcs(coil, right);
  uint64_t pairs = 0, permutations = 0;
  for (auto &u : a)
    for (auto &v : b) {
      if (left == right && u > v)
        continue;
      std::vector<int> p(u.rbegin(), u.rend());
      p.insert(p.end(), v.begin() + 1, v.end());
      Pivot solver;
      ++pairs;
      if (solver.solve(p, left)) {
        for (int i = left + 1; i < p.size(); i++)
          p[i] = solver.mapped[p[i]];
        if (!valid(p))
          return 4;
        std::cout << "FOUND";
        for (int z : p)
          std::cout << " " << z;
        std::cout << std::endl;
        return 0;
      }
      if (solver.leaves != 362880)
        return 5;
      permutations += solver.leaves;
    }
  std::cout << "arcs " << a.size() << " " << b.size() << " pairs " << pairs
            << " permutations " << permutations << std::endl;
}
