#pragma once
#include "star_board.hpp"
#include <algorithm>
#include <bit>
#include <vector>

// Enumerate each connected three-centre set once. A middle is unique in a
// chain; for a triangle choose its least centre.
template <class Visitor>
void kernel_triples(Board& board,Visitor visit){
    for(int centre=0;centre<board.n;centre++){
        std::vector<int> near;
        for(int v=0;v<board.n;v++)
            if(v!=centre && std::popcount(unsigned(v^centre))<=2)near.push_back(v);
        board.star(centre);
        for(int j=0;j<int(near.size());j++){
            int b=near[j];board.star(b);
            for(int i=0;i<j;i++){
                int a=near[i];
                if(std::popcount(unsigned(a^b))<=2 && std::min(a,b)<centre)continue;
                board.star(a);visit(centre,b,a);board.star(a);
            }
            board.star(b);
        }
        board.star(centre);
    }
}
