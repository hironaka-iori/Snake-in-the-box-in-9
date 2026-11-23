// A subset of a path is a linear forest. Add arbitrary vertices by growing or merging components.
int components(const Bits &set, array<int,512> &label,array<int,512> &deg){
    label.fill(-1);deg.fill(0);int count=0;
    for(int x=0;x<512;x++)if(set[x])for(int a=0;a<9;a++)deg[x]+=set[x^(1<<a)];
    for(int x=0;x<512;x++)if(set[x]&&label[x]==-1){
        vector<int> q{x};label[x]=count;int twice=0;
        for(size_t j=0;j<q.size();j++){int z=q[j];twice+=deg[z];if(deg[z]>2)return -1;
            for(int a=0;a<9;a++){int y=z^(1<<a);if(set[y]&&label[y]<0){label[y]=count;q.push_back(y);}}
        }
        if(twice!=2*((int)q.size()-1))return -1;
        count++;
    }return count;
}
bool grow(Bits set,int remain,vector<int>&out){
    array<int,512> lab,deg;int c=components(set,lab,deg);
    if(c<1||c>remain+1)return false;
    if(remain==0){
        int x=0;while(x<512&&(!set[x]||deg[x]>1))x++;
        int prev=-1;while(x<512){out.push_back(x);int next=512;for(int a=0;a<9;a++){int y=x^(1<<a);if(y!=prev&&set[y]){next=y;break;}}prev=x;x=next;}
        return out.size()==set.count();
    }
    Bits candidates;
    for(int x=0;x<512;x++)if(set[x]&&deg[x]<2)for(int a=0;a<9;a++)candidates.set(x^(1<<a));
    candidates&=~set;
    for(int y=0;y<512;y++)if(candidates[y]){
        int first=-1,h=0;bool ok=true;
        for(int a=0;a<9;a++){int x=y^(1<<a);if(!set[x])continue;
            if(++h>2||deg[x]>=2||lab[x]==first){ok=false;break;}first=lab[x];
        }
        if(!ok||c+1-h>remain)continue;
        set.set(y);if(grow(set,remain-1,out))return true;set.reset(y);
    }return false;
}
bool complete_forest(const vector<int>&basis,const vector<int>&pts,int target,int id){
    array<int,512> coord{};vector<int> space{0};
    for(int a=0;a<9;a++){int n=space.size();for(int j=0;j<n;j++){int y=space[j]^basis[a];coord[y]=coord[space[j]]^(1<<a);space.push_back(y);}}
    Bits set;for(int x:pts)set.set(coord[x]);
    vector<int> p;if(!grow(set,target+1-(int)pts.size(),p))return false;
    cout<<"FOUND "<<id<<" locked -1 basis";for(int v:basis)cout<<" "<<v;cout<<" path";for(int v:p)cout<<" "<<v;cout<<endl;return true;
}
