// Rebuild every contraction directly from the selected incidence masks.
// Input is one identifier and 96 same-parity cube addresses per row.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <vector>

using Masks = std::array<unsigned short, 512>;
std::array<int, 512> first{}, second{};

void insert(Masks& masks, int vertex) {
    for (int bit = 1; bit < 512; bit *= 2)
        masks[vertex ^ bit] |= bit;
}

struct Counts { int isolated, leaves; };

Counts count(const Masks& masks, const std::vector<int>& opposite, const std::vector<int>& selected) {
    std::array<int, 512> degrees{};
    for (int u : opposite) {
        int mask = masks[u];
        if (!first[mask]) continue;
        int alternate = u ^ mask;
        // The only other common neighbour of the corresponding pair is alternate.
        // If it has degree two, it labels the same edge of the simple contraction.
        if (alternate < u && first[masks[alternate]]) continue;
        ++degrees[u ^ first[mask]];
        ++degrees[u ^ second[mask]];
    }
    Counts answer{};
    for (int v : selected) {
        answer.isolated += degrees[v] == 0;
        answer.leaves += degrees[v] == 1;
    }
    return answer;
}

int main() {
    for (int i = 1; i < 512; i *= 2)
        for (int j = 1; j < i; j *= 2) {
            first[i+j] = i;
            second[i+j] = j;
        }
    int id;
    while (std::cin >> id) {
        std::array<int, 96> original;
        std::array<bool, 512> used{};
        for (auto& v : original) {
            if (!(std::cin >> v) || v < 0 || v >= 512 || used[v]) return 2;
            used[v] = true;
        }
        std::vector<int> additions, opposite;
        for (int v = 0; v < 512; ++v) {
            int parity = 0;
            for (int bit = 1; bit < 512; bit *= 2)
                parity ^= !!((original[0] ^ v) & bit);
            if (parity) opposite.push_back(v);
            else if (!used[v]) additions.push_back(v);
        }
        if (opposite.size() != 256 || additions.size() != 160) return 3;
        unsigned pairs = 0, hits = 0;
        for (int removed : original) {
            std::vector<int> retained;
            Masks base_masks{};
            for (int v : original) if (v != removed) {
                retained.push_back(v);
                insert(base_masks, v);
            }
            // Both one-addition prefixes of a viable unordered pair must pass.
            std::vector<int> possible;
            for (int a : additions) {
                auto masks = base_masks;
                insert(masks, a);
                auto here = retained;
                here.push_back(a);
                auto c = count(masks, opposite, here);
                if (2*c.isolated + c.leaves <= 4) possible.push_back(a);
            }
            for (unsigned i = 0; i < possible.size(); ++i)
                for (unsigned j = 0; j < i; ++j) {
                    ++pairs;
                    auto masks = base_masks;
                    insert(masks, possible[i]);
                    insert(masks, possible[j]);
                    auto here = retained;
                    here.push_back(possible[i]);
                    here.push_back(possible[j]);
                    auto c = count(masks, opposite, here);
                    if (!c.isolated && c.leaves <= 2) {
                        std::cout << id << ' ' << removed << ' ' << possible[j] << ' ' << possible[i] << '\n';
                        ++hits;
                    }
                }
        }
        std::cerr << id << ' ' << pairs << ' ' << hits << '\n';
    }
}
