// One input row gives a base identifier and its 96 vertices.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <vector>

constexpr int n = 512;
static std::array<std::array<int, 2>, n> two_bits;

struct Contraction {
    std::array<int, n> mask{}, degree{};
    std::array<bool, n> selected{};
    unsigned char support[n][n]{};
    int isolated = 0, leaves = 0;

    void count_degree(int d, int change) {
        if (d == 0) isolated += change;
        if (d == 1) leaves += change;
    }
    void change_degree(int v, int change) {
        count_degree(degree[v], -1);
        degree[v] += change;
        count_degree(degree[v], 1);
    }
    void change_label(int z, int m, int delta) {
        auto bits = two_bits[m];
        if (bits[0] == 0) return;
        int v = z ^ bits[0], w = z ^ bits[1];
        if (v > w) std::swap(v, w);
        int before = support[v][w];
        support[v][w] += delta;
        if (before == 0 || support[v][w] == 0) {
            change_degree(v, delta);
            change_degree(w, delta);
        }
    }
    void toggle(int v) {
        bool adding = !selected[v];
        if (adding) ++isolated;
        for (int bit = 1; bit < n; bit <<= 1) {
            int z = v ^ bit;
            change_label(z, mask[z], -1);
            mask[z] ^= bit;
            change_label(z, mask[z], 1);
        }
        if (!adding) --isolated;
        selected[v] = adding;
    }
};

int main() {
    for (int i = 1; i < n; i <<= 1)
        for (int j = 2*i; j < n; j <<= 1) two_bits[i+j] = {i, j};
    int id;
    while (std::cin >> id) {
        Contraction graph;
        std::array<int, 96> base;
        for (int &v : base) {
            if (!(std::cin >> v) || v < 0 || v >= n || graph.selected[v]) return 2;
            graph.toggle(v);
        }
        std::vector<int> outside;
        for (int v = 0; v < n; ++v) {
            int difference = v ^ base.front(), parity = 0;
            while (difference) { parity ^= 1; difference &= difference-1; }
            if (!parity && !graph.selected[v]) outside.push_back(v);
        }
        if (outside.size() != 160) return 3;
        std::uint64_t by_deletion=0, by_first=0, by_final=0, survivors=0;
        for (int d : base) {
            graph.toggle(d);
            if (2*graph.isolated + graph.leaves > 6) {
                by_deletion += 160*159/2;
            } else for (int i=0; i<159; ++i) {
                int a=outside[i];
                graph.toggle(a);
                if (2*graph.isolated + graph.leaves > 4) {
                    by_first += 159-i;
                } else for (int j=i+1; j<160; ++j) {
                    int b=outside[j];
                    graph.toggle(b);
                    if (graph.isolated || graph.leaves>2) ++by_final;
                    else {
                        ++survivors;
                        std::cout << id << ' ' << d << ' ' << a << ' ' << b << '\n';
                    }
                    graph.toggle(b);
                }
                graph.toggle(a);
            }
            graph.toggle(d);
        }
        std::cerr << id << ' ' << by_deletion << ' ' << by_first << ' '
                  << by_final << ' ' << survivors << '\n';
    }
}
