#include <algorithm>
#include <array>
#include <bit>
#include <iostream>
#include <vector>

namespace {
using Mask = unsigned;
constexpr int side = 16;
using Table = std::array<std::array<int, side + 1>, side + 1>;

class Census {
public:
    Census() {
        for (auto& row : maxima_) row.fill(-1);
        std::array<int, 32> even_index{};
        int even_count = 0;
        for (unsigned vertex = 0; vertex < 32; ++vertex) {
            if (std::popcount(vertex) % 2 == 0) even_index[vertex] = even_count++;
        }
        int odd_index = 0;
        for (unsigned vertex = 0; vertex < 32; ++vertex) {
            if (std::popcount(vertex) % 2 == 0) continue;
            for (int axis = 0; axis < 5; ++axis) {
                const unsigned neighbor = vertex ^ (1u << axis);
                neighborhood_[odd_index] |= 1u << even_index[neighbor];
            }
            ++odd_index;
        }
    }

    Table run() {
        for (Mask black = 0; black < (1u << side); ++black) {
            const int black_count = std::popcount(black);
            int isolated = 0;
            candidates_.clear();
            for (Mask neighbors : neighborhood_) {
                const Mask contacts = neighbors & black;
                const int degree = std::popcount(contacts);
                if (degree == 0) ++isolated;
                if (degree == 1 || degree == 2) candidates_.push_back(contacts);
            }
            isolated_ = isolated;
            row_ = &maxima_[black_count];
            for (int i = 0; i < side; ++i) parent_[i] = i;
            search(0, 0, 0, 0, 0);
        }
        return maxima_;
    }

private:
    int root(int vertex) const {
        while (parent_[vertex] != vertex) vertex = parent_[vertex];
        return vertex;
    }

    void search(unsigned index, int white, int edges, Mask used, Mask saturated) {
        if (index == candidates_.size()) {
            for (int count = white; count <= white + isolated_; ++count) {
                (*row_)[count] = std::max((*row_)[count], edges);
            }
            return;
        }

        search(index + 1, white, edges, used, saturated);
        const Mask contacts = candidates_[index];
        if (saturated & contacts) return;
        const int degree = std::popcount(contacts);
        const Mask new_saturated = saturated | (used & contacts);
        if (degree == 1) {
            search(index + 1, white + 1, edges + degree, used | contacts, new_saturated);
            return;
        }

        const int first = root(std::countr_zero(contacts));
        const int second = root(std::countr_zero(contacts & (contacts - 1)));
        if (first == second) return;
        parent_[second] = first;
        search(index + 1, white + 1, edges + degree, used | contacts, new_saturated);
        parent_[second] = second;
    }

    Table maxima_{};
    std::array<Mask, side> neighborhood_{};
    std::array<int, side> parent_{};
    std::vector<Mask> candidates_;
    std::array<int, side + 1>* row_{};
    int isolated_{};
};
}  // namespace

int main() {
    const Table table = Census().run();
    for (int black = 0; black <= side; ++black) {
        for (int white = 0; white <= side; ++white) {
            if (table[black][white] != table[white][black]) return 1;
            std::cout << black << ' ' << white << ' ' << table[black][white] << '\n';
        }
    }
}
