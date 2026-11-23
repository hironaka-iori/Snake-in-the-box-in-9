// Beam over genuine Q10 snakes. Track the longest induced Q9 suffix for all 45
// axis identifications, allowing the beginning of the projected window to slide.
#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <cmath>
#include <fstream>
#include <iostream>
#include <random>
#include <string>
#include <unordered_set>
#include <vector>
using namespace std;
using Path=vector<int>;
array<int,45> masks{};
array<array<int,9>,45> offsets{};
uint64_t salts[1024];
int fold_point(int x,int m){int b=bit_floor(unsigned(m));if(x&b)x^=m;return (x&(b-1))|((x/b/2)*b);}
bool valid(const Path& p,int dim){
    for(int i=0;i<int(p.size());i++){if(p[i]<0||p[i]>=(1<<dim))return false;
        for(int j=0;j<i;j++){int d=popcount(unsigned(p[i]^p[j]));if(!d||((d==1)!=(i==j+1)))return false;}}
    return true;
}
struct State{
    array<short,1024> time{};
    array<unsigned short,515> sequence{};
    array<short,45> first{};
    short n=1;
    uint64_t hash=0;
    State(){time.fill(-1);time[0]=0;}
    bool legal(int x)const{
        if(time[x]>=0)return false;
        for(int a=1;a<1024;a*=2){int j=time[x^a];if(j>=0&&j<n-1)return false;}
        return true;
    }
    void suffixes(int x,array<short,45>& next)const{
        next=first;
        for(int f=0;f<45;f++)
            for(int delta:offsets[f])next[f]=max<int>(next[f],time[x^delta]+1);
    }
    void push(int x,const array<short,45>& next){
        sequence[n]=x;time[x]=n++;first=next;hash^=salts[x];
    }
    Path window(int f)const{Path p;for(int i=first[f];i<n;i++)p.push_back(fold_point(sequence[i],masks[f]));return p;}
};
struct Candidate{double fitness;int parent,x;array<short,45> first;};
int main(int argc,char** argv){
    if(argc!=7)return 2;mt19937_64 rng(stoull(argv[1]));int runs=stoi(argv[2]),width=stoi(argv[3]),goal=stoi(argv[4]),mode=stoi(argv[5]);ifstream in(argv[6]);
    int f=0;for(int a=1;a<1024;a*=2)for(int b=1;b<a;b*=2){int m=a|b;masks[f]=m;offsets[f][0]=m;int j=1;for(int c=1;c<1024;c*=2)if(!(c&m))offsets[f][j++]=m|c;f++;}
    for(auto& salt:salts)salt=rng();
    vector<string> words;string w;while(in>>w){assert(w.size()==191);words.push_back(w);}assert(words.size());
    uint64_t nodes=0,checks=0;int best=0,post=0,trialHits=0;
    for(int r=0;r<runs;r++){
        int row=rng()%words.size();w=words[row];if(rng()%2)reverse(w.begin(),w.end());
        int prefix=mode==2?18:(mode==1?165:85+rng()%107);
        int start=rng()%(192-prefix);int bit=1<<(rng()%9),mainFold=find(masks.begin(),masks.end(),bit|512)-masks.begin();
        State root;for(int j=start;j<start+prefix;j++){
            int z=1<<(w[j]-'0');if(z==bit&&rng()%2)z=512;
            int x=root.sequence[root.n-1]^z;assert(root.legal(x));array<short,45> right;root.suffixes(x,right);root.push(x,right);
        }
        assert(root.first[mainFold]==0);
        vector<State> beam{root};int last=prefix,depth=mode==2?60:min(360,prefix+115);
        double noise=1+(rng()%1900)/100.,secondWeight=(rng()%61)/100.;bool secondary=r%5==2;
        for(int t=prefix+1;t<=depth&&!beam.empty();t++){
            vector<Candidate> choices;unordered_set<uint64_t> visited;
            for(int k=0;k<int(beam.size());k++){auto& s=beam[k];int old=s.sequence[s.n-1];
                for(int b=1;b<1024;b*=2){int x=old^b;if(!s.legal(x))continue;
                    uint64_t key=(s.hash^salts[x])*0x9e3779b97f4a7c15ULL+salts[x];
                    if(!visited.insert(key).second)continue;
                    Candidate c{0,k,x,{}};s.suffixes(x,c.first);nodes++;
                    int top=-1,runner=-1,which=-1,alt=-1;
                    for(int g=0;g<45;g++){int len=t-c.first[g];if(g!=mainFold)alt=max(alt,len);
                        if(len>top){runner=top;top=len;which=g;}else runner=max(runner,len);}
                    if(mode==2||top>best||top>=goal){
                        State next=s;next.push(x,c.first);auto p=next.window(which);assert(valid(p,9)&&int(p.size())==top+1);
                        if(mode==2){
                            for(int g=0;g<45;g++){
                                int begin=0;
                                for(int j=0;j<next.n;j++)for(int i=begin;i<j-1;i++){
                                    int dif=fold_point(next.sequence[i]^next.sequence[j],masks[g]);
                                    if(popcount(unsigned(dif))<=1)begin=i+1;
                                }
                                assert(begin==c.first[g]);checks++;
                            }
                        }
                        if(top>best||top>=goal){best=max(best,top);cout<<"PATH "<<r<<" "<<row<<" "<<start<<" "<<prefix<<" "<<t<<" "<<masks[which]<<" "<<top;
                            for(int v:p)cout<<" "<<v;cout<<endl;}
                        if(top>=goal){trialHits++;if(mode==0)return 0;if(mode==1)goto done;}
                    }
                    double progress=secondary?(.42*top+.58*alt):top;
                    c.fitness=progress+secondWeight*runner+noise*generate_canonical<double,32>(rng);choices.push_back(c);
                }
            }
            if(choices.size()>width){nth_element(choices.begin(),choices.begin()+width,choices.end(),[](const auto& a,const auto& b){return a.fitness>b.fitness;});choices.resize(width);}
            vector<State> next;next.reserve(choices.size());for(auto& c:choices){auto& state=next.emplace_back(beam[c.parent]);state.push(c.x,c.first);}
            beam.swap(next);if(!beam.empty())last=t;
        }
        done:post=max(post,last);if(r%10==9)cout<<"AT "<<r+1<<" "<<nodes<<" "<<best<<" "<<post<<" "<<checks<<" "<<trialHits<<endl;
    }
    cout<<"DONE "<<runs<<" "<<nodes<<" "<<best<<" "<<post<<" "<<checks<<" "<<trialHits<<endl;
}
