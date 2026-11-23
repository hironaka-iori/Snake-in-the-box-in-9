#define Q9_FIBER_LIBRARY
#include "search_q9_three_axis_recolor.cpp"
#include <random>
// Join two different observed paths. Align coordinate names from transition
// agreement near the joint, then let the hidden Q3 layers vary globally.
struct Donor{Path v,word;};
int main(int argc,char**argv){
 if(argc!=4)return 2;int trials=stoi(argv[1]),cap=stoi(argv[2]);mt19937 rng(stoi(argv[3]));
 vector<Donor> bank;string w;
 while(cin>>w){
    if(w.size()<189||w.size()>191)return 2;
    for(int orientation=0;orientation<2;orientation++){
        Donor d;d.v={0};for(char c:w){int bit=c-'0';d.word.push_back(bit);d.v.push_back(d.v.back()^(1<<bit));}
        bank.push_back(d);reverse(w.begin(),w.end());
    }
 }
 vector<int> masks;for(int m=1;m<512;m++)if(popcount(unsigned(m))==3)masks.push_back(m);
 uint64_t checked=0,cutoff=0;
 for(int trial=0;trial<trials;trial++){
    int id1=rng()%bank.size(),id2=rng()%bank.size();if(id1/2==id2/2)continue;
    auto &a=bank[id1],&b=bank[id2];
    int pre=52+rng()%88,post=191-pre;
    // Sample both endpoint-rooted and interior donors.
    int end=pre+(rng()%3==0?rng()%(a.word.size()-pre+1):0);
    int start=b.word.size()-post-(rng()%3==0?rng()%(b.word.size()-post+1):0);
    array<array<int,9>,9> weights{};
    for(int off=-48;off<48;off++)if(end+off>=0&&end+off<a.word.size()&&start+off>=0&&start+off<b.word.size())
        weights[b.word[start+off]][a.word[end+off]]+=50-abs(off);
    array<int,9> perm;perm.fill(-1);int used=0;
    for(int j=0;j<9;j++){
        int best=-1,x=-1,y=-1;
        for(int k=0;k<9;k++)if(perm[k]<0)for(int s=0;s<9;s++)if(!(used&(1<<s))){
            int score=weights[k][s]*16+int(rng()%15);if(score>best){best=score;x=k;y=s;}
        }
        perm[x]=y;used|=1<<y;
    }
    if(rng()%3==0)swap(perm[rng()%9],perm[rng()%9]);
    int mask=masks[rng()%masks.size()];
    Path q(a.v.begin()+end-pre,a.v.begin()+end+1);
    q.push_back(q.back()^(1<<(rng()%9)));for(int k=start;k<start+post;k++)q.push_back(q.back()^(1<<perm[b.word[k]]));
    assert(q.size()==193);Fiber f(q,mask,cap);int r=f.run();checked++;cutoff+=r<0;
    if(r==1){cout<<"FOUND "<<trial<<" "<<mask;for(int v:f.result)cout<<" "<<v;cout<<endl;return 0;}
    if((trial+1)%50000==0)cout<<"AT "<<trial+1<<" "<<checked<<" "<<cutoff<<endl;
 }
 cout<<"DONE "<<checked<<" "<<cutoff<<endl;
}
