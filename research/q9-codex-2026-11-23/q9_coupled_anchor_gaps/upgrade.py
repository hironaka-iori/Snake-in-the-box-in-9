from pathlib import Path
f=Path(__file__).parent/'forest.cpp'
s=f.read_text().replace('vector<int> e;vector<Gap>', 'int tips;vector<int> ref,e;vector<Gap>',1)
s=s.replace('vector<int> data,vector<Gap> gaps,int cap,mt19937& rng):e(data)', 'vector<int> data,vector<int> orig,vector<Gap> gaps,int cap,int addtips,mt19937& rng):tips(addtips),ref(orig),e(data)')
s=s.replace('for(auto &x:g)for(int i=x.l;i<=x.r;i++)if(!used[e[i]])lost[i>=mid]=true;', 'for(int i=0;i<(int)ref.size();i++)if(!used[ref[i]])lost[i>=mid]=true;')
s=s.replace('  return true;\n }\n bool dfs', '''  if(tips){
   int left=-1,right=-1;for(int d=0;d<9;d++){int a=v.front()^(1<<d),b=v.back()^(1<<d);
    if(load[a]==1)left=a;if(load[b]==1)right=b;}
   if(tips==2&&(left<0||right<0))return false;
   if(tips==1&&left<0&&right<0)return false;
   if(left>=0)w.insert(w.begin(),left);
   if(right>=0&&(tips==2||left<0))w.push_back(right);
  }
  return true;
 }
 bool dfs''')
s=s.replace('int n=e.size(),mid=n/2;', 'int n=e.size(),mid=n/2;')
s=s.replace('if((mode==0&&typ!=0)||(mode>0&&typ!=1))continue;', 'if((mode==0||mode==3||mode==5)?typ!=0:typ!=1)continue;')
s=s.replace('int diff=target/2+1-n;', '''int transform=0,tx=0,axisA=0,axisB=0;
    if(mode>=3){
     int from=g.front().r+1,to=g.back().l-1;
     if(from>to)continue;
     transform=1+randn(4);axisA=randn(9);axisB=randn(8);if(axisB>=axisA)axisB++;
     tx=work[from+randn(to-from+1)];
     int mask=(1<<axisA)|(1<<axisB);
     for(int i=from;i<=to;i++){
      int base=work[i]^tx;
      if(transform<4&&((base>>axisA)^(base>>axisB))&1)work[i]^=mask;
      if(transform>=3)work[i]^=mask;
     }
     if(work==e)continue;
    }
    int tips=target%2?1:(mode==3||mode==4?2:0);
    int diff=(target-tips)/2+1-n;''')
s=s.replace('if(!good||!unique.insert(key).second)continue;', 'if(transform)key.insert(key.end(),{transform,axisA,axisB,((tx>>axisA)^(tx>>axisB))&1});if(!good||!unique.insert(key).second)continue;')
s=s.replace('Solver s(work,g,cap,rng);','Solver s(work,mode==2?work:e,g,cap,tips,rng);')
f.write_text(s)
