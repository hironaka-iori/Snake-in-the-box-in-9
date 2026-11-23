#include <algorithm>
#include <array>
#include <bit>
#include <deque>
#include <iostream>
#include <sstream>
#include <string>
#include <unordered_set>
#include <vector>

using Path = std::vector<int>;

bool valid(const Path &p) {
  for (size_t i = 0; i < p.size(); ++i) {
    if (p[i] < 0 || p[i] >= 512)
      return false;
    for (size_t j = 0; j < i; ++j) {
      int distance = std::popcount(unsigned(p[i] ^ p[j]));
      if (!distance || (distance == 1) != (j + 1 == i))
        return false;
    }
  }
  return true;
}

std::string signature(const Path &p) {
  std::string steps;
  for (size_t i = 1; i < p.size(); ++i)
    steps.push_back(std::countr_zero(unsigned(p[i] ^ p[i - 1])));
  auto normalize = [](std::string word) {
    std::array<int, 9> label;
    label.fill(-1);
    int count = 0;
    for (char &axis : word) {
      auto &n = label[static_cast<unsigned char>(axis)];
      if (n < 0)
        n = count++;
      axis = static_cast<char>(n);
    }
    return word;
  };
  auto forward = normalize(steps);
  std::reverse(steps.begin(), steps.end());
  return std::min(forward, normalize(steps));
}

int main(int argc, char **argv) {
  if (argc != 4) {
    std::cerr << "usage: enumerate_q9_local_paths floor export_length "
                 "expansion_limit < vertex_rows\n";
    return 2;
  }
  const int floor = std::stoi(argv[1]), keep = std::stoi(argv[2]);
  const size_t limit = std::stoull(argv[3]);
  if (floor < 2 || keep < floor || limit == 0)
    return 2;
  std::deque<std::string> queue;
  std::unordered_set<std::string> visited;
  auto add = [&](const Path &p) {
    auto id = signature(p);
    if (!visited.insert(id).second)
      return;
    if (int(id.size()) == keep || id.size() >= 192) {
      if (!valid(p))
        std::abort();
      for (int v : p)
        std::cout << v << ' ';
      std::cout << '\n';
    }
    queue.push_back(std::move(id));
  };
  std::string line;
  while (std::getline(std::cin, line)) {
    std::istringstream input(line);
    Path p;
    int v;
    while (input >> v)
      p.push_back(v);
    if (int(p.size()) <= floor || !valid(p))
      return 3;
    add(p);
  }
  size_t expanded = 0;
  while (!queue.empty() && expanded < limit) {
    auto id = std::move(queue.front());
    queue.pop_front();
    ++expanded;
    Path p{0};
    for (int axis : id)
      p.push_back(p.back() ^ (1 << axis));
    std::array<bool, 512> used{};
    std::array<int, 512> degree{};
    for (int x : p) {
      used[x] = true;
      for (int i = 0; i < 9; ++i)
        ++degree[x ^ (1 << i)];
    }
    for (int side = 0; side < 2; ++side) {
      const int end = p.back(), start = p.front(), prev = p[p.size() - 2];
      if (int(id.size()) > floor)
        add(Path(p.begin(), p.end() - 1));
      for (int i = 0; i < 9; ++i) {
        int x = end ^ (1 << i);
        if (!used[x]) {
          if (degree[x] == 1) {
            p.push_back(x);
            add(p);
            p.pop_back();
          }
          if (degree[x] - (std::popcount(unsigned(x ^ start)) == 1) == 1) {
            Path shifted(p.begin() + 1, p.end());
            shifted.push_back(x);
            add(shifted);
          }
        }
        x = prev ^ (1 << i);
        if (!used[x] && degree[x] == 1) {
          p.back() = x;
          add(p);
          p.back() = end;
        }
      }
      std::reverse(p.begin(), p.end());
    }
    for (size_t i = 1; i + 1 < p.size(); ++i) {
      const int orig = p[i], flip = p[i - 1] ^ orig ^ p[i + 1];
      if (!used[flip] && degree[flip] == 2) {
        p[i] = flip;
        add(p);
        p[i] = orig;
      }
    }
  }
  std::cerr << "expanded " << expanded << " remaining " << queue.size() << '\n';
}
