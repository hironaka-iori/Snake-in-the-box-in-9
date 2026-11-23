#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>

using Mask = std::uint32_t;
using Signature = std::array<int, 4>;
using Histogram = std::map<Signature, std::uint64_t>;

std::array<Mask, 32> neighbors;
std::array<int, 32> degree;
Histogram actual;

Mask component(Mask selected, int start) {
    Mask seen = Mask(1) << start;
    for (Mask pending = seen; pending; ) {
        int vertex = std::countr_zero(pending);
        pending &= pending - 1;
        Mask added = neighbors[vertex] & selected & ~seen;
        seen |= added;
        pending |= added;
    }
    return seen;
}

void enumerate(Mask selected, int first, int edges) {
    auto start = component(selected, 0);
    auto end = component(selected, 31);
    ++actual[{std::popcount(selected), edges, std::popcount(start), std::popcount(end)}];
    for (int vertex = first; vertex < 31; ++vertex) {
        Mask links = neighbors[vertex] & selected;
        int count = std::popcount(links);
        if (count > 2) continue;
        bool allowed = true;
        for (Mask adj = links; adj; adj &= adj - 1) {
            int u = std::countr_zero(adj);
            int limit = u == 0 || u == 31 ? 1 : 2;
            if (degree[u] == limit) allowed = false;
        }
        if (!allowed) continue;
        if (count == 2) {
            int u = std::countr_zero(links);
            Mask other = links & (links - 1);
            if (component(selected, u) & other) continue;
            if ((links & start) && (links & end)) continue;
        }
        for (Mask adj = links; adj; adj &= adj - 1) ++degree[std::countr_zero(adj)];
        degree[vertex] = count;
        enumerate(selected | (Mask(1) << vertex), vertex + 1, edges + count);
        degree[vertex] = 0;
        for (Mask adj = links; adj; adj &= adj - 1) --degree[std::countr_zero(adj)];
    }
}

int main(int argc, char** argv) {
    if (argc != 2) return 2;
    std::ifstream file(argv[1]);
    Histogram expected;
    Signature key;
    std::uint64_t count;
    while (file >> key[0] >> key[1] >> key[2] >> key[3] >> count) {
        if (!count || !expected.emplace(key, count).second) return 3;
    }
    if (!file.eof() || expected.empty()) return 3;
    for (int v = 0; v < 32; ++v)
        for (int axis = 0; axis < 5; ++axis)
            neighbors[v] |= Mask(1) << (v ^ (1 << axis));
    enumerate(Mask(1) | (Mask(1) << 31), 1, 0);
    if (actual != expected) {
        std::cerr << "Signature histogram mismatch\n";
        return 4;
    }
    std::uint64_t labelled = 0;
    for (const auto& [_, size] : actual) labelled += size;
    std::cout << "VERIFIED_Q5_OPPOSITE_TERMINAL_SIGNATURES " << actual.size()
              << " labelled " << labelled << '\n';
}
