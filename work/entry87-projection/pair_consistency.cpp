// Close binary relations under every third variable using bitsets of six-bit words.
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <vector>
using namespace std;
using WordSet=uint64_t;
using Rows=array<WordSet,64>;

int main(){
    int n;
    if(!(cin>>n) || n<1 || n>193)return 2;
    vector<WordSet> domains(n);
    for(auto& d:domains)cin>>d;
    vector<vector<Rows>> rel(n,vector<Rows>(n));
    for(int i=0;i<n;++i){
        for(int w=0;w<64;++w)if(domains[i]&(WordSet(1)<<w))rel[i][i][w]=WordSet(1)<<w;
        for(int j=i+1;j<n;++j)for(int word=0;word<64;++word){
            WordSet supplied;cin>>supplied;
            WordSet words=(domains[i]&(WordSet(1)<<word)) ? supplied&domains[j] : 0;
            rel[i][j][word]=words;
            while(words){
                int v=countr_zero(words);words&=words-1;
                rel[j][i][v]|=WordSet(1)<<word;
            }
        }
    }
    if(!cin)return 2;
    int sweeps=0,total=0,empty_i=-1,empty_j=-1;
    bool changed=true;
    while(changed && empty_i<0){
        changed=false;
        ++sweeps;
        for(int k=0;k<n && empty_i<0;++k)for(int i=0;i<n && empty_i<0;++i){
            if(i==k)continue;
            for(int j=i+1;j<n && empty_i<0;++j){
                if(j==k)continue;
                WordSet can_start=0;
                for(WordSet scan=domains[i];scan;scan&=scan-1){
                    int a=countr_zero(scan);
                    WordSet old=rel[i][j][a];
                    if(!old)continue;
                    WordSet need=old;
                    for(WordSet mid=rel[i][k][a];mid && need;mid&=mid-1){
                        need&=~rel[k][j][countr_zero(mid)];
                    }
                    if(need){
                        changed=true;
                        total+=popcount(need);
                        rel[i][j][a]&=~need;
                        while(need){
                            int b=countr_zero(need);need&=need-1;
                            rel[j][i][b]&=~(WordSet(1)<<a);
                        }
                    }
                    if(rel[i][j][a])can_start|=WordSet(1)<<a;
                }
                if(!can_start){
                    empty_i=i;empty_j=j;
                }
            }
        }
    }
    cout<<sweeps<<' '<<total<<' '<<empty_i<<' '<<empty_j<<'\n';
    if(empty_i>=0)return 0;
    for(int i=0;i<n;++i){
        WordSet kept=domains[i];
        for(WordSet scan=domains[i];scan;scan&=scan-1){
            int a=countr_zero(scan);
            for(int j=0;j<n;++j)if(!rel[i][j][a]){
                kept&=~(WordSet(1)<<a);
                break;
            }
        }
        cout<<kept<<' ';
    }
    cout<<'\n';
}
