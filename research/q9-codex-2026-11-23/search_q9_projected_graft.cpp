// Graft independently projected arms and build the entire joining arc inside Q9.
#define Q9_PROJECTED_GAP_LIBRARY
#include "search_q9_free_projected_gaps.cpp"
struct Donor{Path p,w;};
int main(int argc,char**argv){
 if(argc!=8)return 2;
 int runs=stoi(argv[1]),target=stoi(argv[2]),cross=stoi(argv[3]),cc=stoi(argv[4]),bc=stoi(argv[5]),smax=stoi(argv[6]);mt19937 rng(stoi(argv[7]));
 vector<Donor> parents;string word;
 while(cin>>word){if(word.size()<target-4||word.size()>target)return 2;
    for(int r=0;r<2;r++){
        Donor d;d.p={0};for(char x:word){d.w.push_back(x-'0');d.p.push_back(d.p.back()^(1<<(x-'0')));}
        parents.push_back(d);reverse(word.begin(),word.end());
    }
 }
 Stats st;Path masks;for(int m=1;m<512;m++)if(popcount(unsigned(m))==3)masks.push_back(m);
 for(int k=0;k<runs;k++){
    int i=rng()%parents.size(),j=i;
    if(cross){do{j=rng()%parents.size();}while(i/2==j/2);}
    auto &a=parents[i],&b=parents[j];int gap=4+rng()%(smax-3),first=1+rng()%(target-gap-1),tail=target-first-gap;
    if(first>a.w.size()||tail>b.w.size()){k--;continue;}
    int pb=b.w.size()-tail,end=first;
    array<int,9> perm; iota(perm.begin(),perm.end(),0);
    if(cross){
        int votes[9][9]{};
        for(int t=-32;t<32;t++)if(pb+t>=0&&pb+t<b.w.size()&&end+gap+t>=0&&end+gap+t<a.w.size())
            votes[b.w[pb+t]][a.w[end+gap+t]]+=33-abs(t);
        int rows=511,cols=511;
        while(rows){
            int bx=0,by=0,best=-1;
            for(int x=0;x<9;x++)if(rows&(1<<x))for(int y=0;y<9;y++)if(cols&(1<<y)){
                int value=votes[x][y]*16+int(rng()%16);if(value>best){best=value;bx=x;by=y;}
            }
            perm[bx]=by;rows^=1<<bx;cols^=1<<by;
        }
    }
    int mask=masks[rng()%84];
    Path q(target+1);copy_n(a.p.begin(),first+1,q.begin());
    int pivot=a.p[min<int>(a.w.size(),first+gap-(target-int(a.w.size())))];
    int mode=rng()%5;if(mode==1||mode==2)pivot^=1<<(rng()%9);
    if(mode==2)pivot^=1<<(rng()%9);
    if(mode==3&&cross)pivot=q[first]^(rng()%512);
    q[first+gap]=pivot;
    for(int t=0;t<tail;t++)q[first+gap+1+t]=q[first+gap+t]^(1<<perm[b.w[pb+t]]);
    vector<Gap> holes{{first,first+gap}};
    if(rng()%2){
       int at=rng()%target,sz=3+rng()%10;
       if(at+sz<first || (at>first+gap && at+sz<=target))holes.push_back({at,at+sz});
       if(holes.size()==2 && holes[1].first<first)swap(holes[0],holes[1]);
    }
    Path result;
    if(search(q,mask,holes,cc,bc,st,result)){cout<<"FOUND "<<i<<" "<<j<<" "<<target;for(int x:result)cout<<" "<<x;cout<<endl;return 0;}
    if((k+1)%10000==0)cout<<"AT "<<st.layouts<<" "<<st.colorings<<" "<<st.colorLimits<<" "<<st.bridgeLimits<<" "<<st.bridgeNodes<<endl;
 }
 cout<<"DONE "<<st.layouts<<" "<<st.colorings<<" "<<st.colorLimits<<" "<<st.bridgeLimits<<" "<<st.bridgeNodes<<endl;
}
