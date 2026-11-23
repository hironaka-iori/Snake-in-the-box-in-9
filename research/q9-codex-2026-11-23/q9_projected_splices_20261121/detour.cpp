#define Q9_OMIT_SPLICE_MAIN
#include "search.cpp"
#undef main
struct Detour{
 Engine &engine;int rootcap,gapmax,extra,lo=0,hi=0,project_axis=0,row_id=0,leaves=0,budget=0;long long gaps=0,viable=0,truncated=0,total=0;
 Path base,mid;bool busy[256]={};mt19937 rng;int permutations[20][8];
 Detour(Engine&e,int cap,int gm,int ex,int seed):engine(e),rootcap(cap),gapmax(gm),extra(ex),rng(seed){}
 bool outside(int a,int b){
  DSU colors;int where[256];fill(where,where+256,-1);bool hit[300]={};
  for(int k=0;k<int(base.size());k++)if(k<=a||k>=b){int v=base[k];if(where[v]>=0)return false;where[v]=k;}
  for(int k=0;k<int(base.size());k++)if(k<=a||k>=b)for(int d=1;d<256;d*=2){int j=where[base[k]^d];if(j<=k+1||(k==a&&j==b))continue;hit[k]=hit[j]=true;if(!colors.link(k,j,1))return false;}
  for(int k=1;k<int(base.size());k++)if(hit[k]&&hit[k-1]&&!colors.link(k-1,k,0))return false;
  for(int k=0;k<256;++k)busy[k]=where[k]>=0;return true;
 }
 void enumerate(int position,int left){
  if(!budget)return;
  int goal=base[hi];
  if(left==1){if(popcount(unsigned(position^goal))!=1)return;
   if((int)mid.size()==hi-lo-1&&equal(mid.begin(),mid.end(),base.begin()+lo+1))return;
   Path q(base.begin(),base.begin()+lo+1);q.insert(q.end(),mid.begin(),mid.end());q.insert(q.end(),base.begin()+hi,base.end());--budget;leaves++;total++;
   Path witness;int z=engine.score(q,engine.goal-1,witness);
   if(z>=engine.goal-1){string key=code9(witness);bool novel=(z==191&&!engine.reference.count(key)&&engine.classes.insert(key).second);
    if(z>engine.best||novel||z>=engine.goal){cout<<"DETOUR "<<z<<" row "<<row_id<<" axis "<<project_axis<<" lo "<<lo<<" hi "<<hi<<" mid";for(int v:mid)cout<<" "<<v;cout<<"\nPATH";for(int v:witness)cout<<" "<<v;cout<<endl;}
    engine.best=max(engine.best,z);if(z>=engine.goal)exit(0);
   }return;
  }
  for(int k:permutations[left]){int q=position^(1<<k);if(busy[q]||popcount(unsigned(q^goal))>left-1)continue;busy[q]=true;mid.push_back(q);enumerate(q,left-1);mid.pop_back();busy[q]=false;if(!budget)break;}
 }
 void run(Path q,int row,int d){
  if(!engine.seen.insert(canon(q)).second)return;++engine.bases;base=std::move(q);project_axis=d;row_id=row;
  vector<pair<int,int>> choices;for(int a=0;a<int(base.size());++a)for(int b=a+2;b<int(base.size())&&b-a<=gapmax;++b)choices.emplace_back(a,b);
  shuffle(choices.begin(),choices.end(),rng);
  for(auto [a,b]:choices){gaps++;if(!outside(a,b))continue;viable++;lo=a;hi=b;budget=rootcap;
   for(auto &axes:permutations){iota(axes,axes+8,0);shuffle(axes,axes+8,rng);}
   vector<int>lengths;for(int n=max(1,b-a-2);n<=b-a+extra;n++)if((n-(b-a))%2==0)lengths.push_back(n);shuffle(lengths.begin(),lengths.end(),rng);
   for(int n:lengths){if(n<popcount(unsigned(base[a]^base[b])))continue;enumerate(base[a],n);if(!budget)break;}
   if(!budget)truncated++;
  }
 }
};
#ifndef Q9_OMIT_DETOUR_MAIN
int main(int argc,char**argv){
 if(argc!=6)return 2;int lim=stoi(argv[1]),gap=stoi(argv[2]),extra=stoi(argv[3]),cap=stoi(argv[4]),seed=stoi(argv[5]);Engine e(0,0,192,seed);Detour d(e,cap,gap,extra,seed);
 ifstream f("q9_four_piece_191_classes.txt");string line;while(getline(f,line))e.reference.insert(line);if(e.reference.size()!=131)return 3;
 for(int row=0;row<lim&&getline(cin,line);row++){Path p;int x;istringstream in(line);while(in>>x)p.push_back(x);for(int k=0;k<9;k++)d.run(project(p,k),row,k);}
 cout<<"DONE bases "<<e.bases<<" gaps "<<d.gaps<<" passed "<<d.viable<<" capped "<<d.truncated<<" candidates "<<d.total<<" prepared "<<e.consistent<<" models "<<e.models<<" best "<<e.best<<" novel191 "<<e.classes.size()<<endl;
}

#endif
