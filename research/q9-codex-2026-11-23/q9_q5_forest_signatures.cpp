#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <map>
#include <string_view>
#include <unordered_set>
#include <vector>

using Mask = std::uint32_t;
using Signature = std::array<int, 22>;

struct Hasher {
    std::size_t operator()(const Signature& signature) const {
        std::size_t value = 0;
        for (int item : signature) value = value * 131 + item;
        return value;
    }
};

std::array<std::array<Mask, 6>, 32> shells;

void build_shells() {
    for (int u = 0; u < 32; ++u)
        for (int v = 0; v < 32; ++v)
            shells[u][std::popcount(unsigned(u ^ v))] |= Mask(1) << v;
}

Mask interior(Mask points) {
    Mask degree_two = 0;
    for (Mask todo = points; todo; todo &= todo - 1) {
        int u = std::countr_zero(todo);
        int d = std::popcount(shells[u][1] & points);
        if (d > 2) return ~Mask(0);
        if (d == 2) degree_two |= Mask(1) << u;
    }
    return degree_two;
}

bool acyclic(Mask points, Mask degree_two) {
    Mask reached = points & ~degree_two;
    for (Mask todo = reached; todo; ) {
        int u = std::countr_zero(todo);
        todo &= todo - 1;
        Mask next = shells[u][1] & points & ~reached;
        reached |= next;
        todo |= next;
    }
    return reached == points;
}

int choose(int n, int k) {
    int result = 1;
    for (int j = 1; j <= k; ++j) result = result * (n-j+1) / j;
    return result;
}

Signature describe(Mask points, Mask degree_two, bool windows) {
    Signature key = {};
    key[0] = std::popcount(points);
    key[1] = std::popcount(degree_two);
    for (int u = 0; u < 32; ++u) {
        if (points & (Mask(1) << u)) {
            for (int d = 1; d <= 5; ++d) key[d+1] += std::popcount(shells[u][d] & points);
        } else {
            int k = std::popcount(shells[u][1] & points);
            for (int j = 3; j <= k; ++j) key[j+4] += choose(k, j);
        }
    }
    for (int j = 2; j <= 6; ++j) key[j] /= 2;
    if (windows) {
        for (Mask remaining = points; remaining; ) {
            Mask component = remaining & (~remaining + 1);
            for (Mask todo = component; todo; ) {
                int u = std::countr_zero(todo);
                todo &= todo - 1;
                Mask add = shells[u][1] & points & ~component;
                component |= add;
                todo |= add;
            }
            int vertices = std::popcount(component);
            for (int lag = 2; lag <= 13 && lag < vertices; ++lag)
                key[lag+8] += vertices-lag;
            remaining &= ~component;
        }
    }
    return key;
}

struct Layer { Mask mask; Mask inner; };

Mask component_at(Mask points, int root) {
    Mask reached = Mask(1) << root;
    for (Mask pending = reached; pending; ) {
        int u = std::countr_zero(pending);
        pending &= pending - 1;
        Mask next = shells[u][1] & points & ~reached;
        reached |= next;
        pending |= next;
    }
    return reached;
}

void opposite_terminal_signatures(const std::vector<Layer>& layers) {
    constexpr Mask terminals = Mask(1) | (Mask(1) << 31);
    std::map<std::array<int, 4>, std::uint64_t> histogram;
    for (const auto [a, inner_a] : layers) {
        if (!(a & 1)) continue;
        for (const auto [b, inner_b] : layers) {
            if (!(b & (Mask(1) << 15)) || ((a & b) & (inner_a | inner_b))) continue;
            Mask points = a | (b << 16);
            Mask degree_two = interior(points);
            assert(degree_two != ~Mask(0));
            if ((degree_two & terminals) || !acyclic(points, degree_two)) continue;
            Mask start = component_at(points, 0);
            if (start & (Mask(1) << 31)) continue;
            int twice_edges = 0;
            for (Mask pending = points; pending; pending &= pending - 1)
                twice_edges += std::popcount(shells[std::countr_zero(pending)][1] & points);
            assert(twice_edges % 2 == 0);
            ++histogram[{std::popcount(points), twice_edges / 2,
                         std::popcount(start), std::popcount(component_at(points, 31))}];
        }
    }
    for (const auto& [key, size] : histogram)
        std::cout << key[0] << ' ' << key[1] << ' ' << key[2] << ' ' << key[3] << ' ' << size << '\n';
}

int main(int argc, char** argv) {
    bool opposite_terminals = argc == 2 && std::string_view(argv[1]) == "--opposite-terminals";
    bool windows = argc == 2 && !opposite_terminals;
    build_shells();
    std::vector<Layer> layers;
    for (Mask mask = 0; mask < (Mask(1) << 16); ++mask) {
        Mask inner = interior(mask);
        if (inner != ~Mask(0) && acyclic(mask, inner)) {
            assert(std::popcount(mask) <= 8);
            layers.push_back({mask, inner});
        }
    }
    assert(layers.size() == 14911);
    if (opposite_terminals) {
        opposite_terminal_signatures(layers);
        return 0;
    }
    std::unordered_set<Signature, Hasher> seen;
    std::uint64_t labelled = 0;
    for (std::size_t i = 0; i < layers.size(); ++i) {
        const auto [a, inner_a] = layers[i];
        for (std::size_t j = i; j < layers.size(); ++j) {
            const auto [b, inner_b] = layers[j];
            Mask cross = a & b;
            if (cross & (inner_a | inner_b)) continue;
            Mask points = a | (b << 16);
            Mask degree_two = interior(points);
            assert(degree_two != ~Mask(0));
            if (std::popcount(cross) > 1 && !acyclic(points, degree_two)) continue;
            seen.insert(describe(points, degree_two, windows));
            labelled += (i == j ? 1 : 2);
        }
    }
    std::vector<Signature> output(seen.begin(), seen.end());
    std::sort(output.begin(), output.end());
    std::cerr << "q4_masks " << layers.size() << " q5_labelled " << labelled
              << " q5_signatures " << output.size() << '\n';
    for (const auto& row : output) {
        for (std::size_t i = 0; i < (windows ? row.size() : 10); ++i)
            std::cout << (i ? " " : "") << row[i];
        std::cout << '\n';
    }
}
