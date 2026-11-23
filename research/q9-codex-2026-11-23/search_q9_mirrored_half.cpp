#include <algorithm>
#include <array>
#include <bitset>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <random>
#include <sstream>
#include <vector>

using Mask = std::bitset<256>;
struct OrbitGraph {
  int dimension, swaps;
  bool centerEdge;
  std::vector<std::array<int, 2>> orbit{{0, 0}};
  std::vector<Mask> adjacent, block;
  int mirror(int x) const {
    for (int i = 0; i < 2 * swaps; i += 2)
      if (((x >> i) ^ (x >> (i + 1))) & 1)
        x ^= 3 << i;
    return centerEdge ? x ^ (1 << (dimension - 1)) : x;
  }
  OrbitGraph(int d, int t, bool edge) : dimension(d), swaps(t), centerEdge(edge) {
    orbit[0][1] = mirror(0);
    for (int x = 1; x < (1 << d); x++)
      if (x < mirror(x) && (!edge || __builtin_popcount(x ^ mirror(x)) > 1))
        orbit.push_back({x, mirror(x)});
    adjacent.resize(orbit.size());
    block.resize(orbit.size());
    for (int i = 0; i < orbit.size(); i++) {
      block[i].set(i);
      for (int j = i + 1; j < orbit.size(); j++) {
        int hits = 0;
        for (int a = 0; a < (i || centerEdge ? 2 : 1); a++)
          for (int b = 0; b < 2; b++)
            hits += __builtin_popcount(orbit[i][a] ^ orbit[j][b]) == 1;
        if (hits) {
          block[i].set(j);
          block[j].set(i);
        }
        // Two edges form a matching, or the two edges at the center.
        // Four edges among two orbits would induce a 4-cycle.
        if (hits == 2) {
          adjacent[i].set(j);
          adjacent[j].set(i);
        }
      }
    }
  }
  std::vector<int> lift(const std::vector<int> &half) const {
    std::vector<int> right{0};
    for (size_t k = 1; k < half.size(); k++) {
      const auto &pair = orbit[half[k]];
      int next =
          __builtin_popcount(right.back() ^ pair[0]) == 1 ? pair[0] : pair[1];
      right.push_back(next);
    }
    std::vector<int> result;
    for (int k = int(right.size()) - 1; k >= (centerEdge ? 0 : 1); k--)
      result.push_back(mirror(right[k]));
    result.insert(result.end(), right.begin(), right.end());
    for (size_t i = 0; i < result.size(); i++)
      for (size_t j = i + 1; j < result.size(); j++) {
        int d = __builtin_popcount(result[i] ^ result[j]);
        if (!d || ((j == i + 1) != (d == 1)))
          std::abort();
      }
    return result;
  }
};
struct State {
  Mask forbidden;
  std::vector<int> path{0};
  int score = 0;
};
int main(int argc, char **argv) {
  bool edge = argc > 1 && std::string(argv[1]) == "--center-edge";
  if (edge) {
    --argc;
    ++argv;
  }
  if (argc != 7 && argc != 8)
    return 2;
  int d = std::stoi(argv[1]), t = std::stoi(argv[2]),
      width = std::stoi(argv[3]), runs = std::stoi(argv[4]),
      target = std::stoi(argv[5]);
  if (d < 2 || d > 9 || t < 1 || 2 * t > d - int(edge) || width < 1 || runs < 1)
    return 2;
  OrbitGraph g(d, t, edge);
  std::mt19937 rng(std::stoul(argv[6]));
  std::vector<std::vector<int>> archive;
  if (argc == 8) {
    std::ifstream input(argv[7]);
    std::string line;
    while (std::getline(input, line)) {
      std::istringstream row(line);
      int swaps, x;
      row >> swaps;
      if (swaps != t)
        continue;
      std::vector<int> path;
      while (row >> x) {
        auto it = std::find(g.orbit.begin(), g.orbit.end(),
                            std::array<int, 2>{std::min(x, g.mirror(x)),
                                               std::max(x, g.mirror(x))});
        if (it == g.orbit.end())
          return 3;
        path.push_back(it - g.orbit.begin());
      }
      if (path.empty() || path.front() != 0)
        return 4;
      auto full = g.lift(path);
      if (int(full.size()) > target) {
        std::cout << "FOUND";
        for (int z : full)
          std::cout << " " << z;
        std::cout << std::endl;
        return 0;
      }
      archive.push_back(std::move(path));
    }
  }
  int best = 0;
  for (int run = 0; run < runs; run++) {
    std::vector<State> beam(1);
    if (!archive.empty() && run % 8 != 0) {
      const auto &start = archive[rng() % archive.size()];
      size_t keep = 1 + (rng() % (start.size() - 1));
      if (run % 4)
        keep = std::max(keep, start.size() / 2);
      beam[0].path.assign(start.begin(), start.begin() + keep);
      for (size_t i = 0; i + 1 < keep; i++)
        beam[0].forbidden |= g.block[start[i]];
    }
    std::vector<int> bestPath;
    int jitter = 2 + run % 9;
    int runBest = 0;
    while (!beam.empty()) {
      std::vector<State> next;
      for (const auto &s : beam) {
        int v = s.path.back();
        auto legal = g.adjacent[v] & ~s.forbidden;
        auto blocked = s.forbidden | g.block[v];
        for (int w = 0; w < g.orbit.size(); w++)
          if (legal[w]) {
            State child{blocked, s.path};
            child.path.push_back(w);
            int edges = 2 * (child.path.size() - 1) + int(edge);
            if (edges > runBest) {
              runBest = edges;
              bestPath = child.path;
            }
            if (edges > best) {
              auto p = g.lift(child.path);
              best = edges;
              if (edges >= target - 24 || edge) {
                std::cout << "HALF " << t;
                for (int z : child.path)
                  std::cout << " " << g.orbit[z][0];
                std::cout << std::endl;
              }
              if (edges >= target) {
                std::cout << "FOUND";
                for (int z : p)
                  std::cout << " " << z;
                std::cout << std::endl;
                return 0;
              }
            }
            auto future = g.adjacent[w] & ~blocked;
            if (!future.any())
              continue;
            child.score = -int((blocked | g.block[w]).count()) * 8 +
                          int(rng() % (jitter * 8)) +
                          int(future.count()) * (run % 4);
            next.push_back(std::move(child));
          }
      }
      if (next.size() > width) {
        std::nth_element(
            next.begin(), next.begin() + width, next.end(),
            [](const State &a, const State &b) { return a.score > b.score; });
        next.resize(width);
      }
      beam.swap(next);
    }
    if (!bestPath.empty() && runBest >= best - 8) {
      if (archive.size() < 2048)
        archive.push_back(bestPath);
      else
        archive[rng() % archive.size()] = bestPath;
    }
    std::cout << "run " << run << " edges " << runBest << " best " << best
              << std::endl;
  }
}
