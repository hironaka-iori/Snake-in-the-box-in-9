// Delay checking connectivity until all extra vertices have been added.
struct DirectFill {
    array<unsigned char,512> occupied{},degrees{};
    vector<int> trail,answer;
    int edgeCount=0,goal=0;
    void toggle(int x,bool add) {
        occupied[x]=add;
        int s=add?1:-1;edgeCount+=s*degrees[x];
        for(int a=0;a<9;a++)degrees[x^(1<<a)]+=s;
    }
    bool finish() {
        if(edgeCount!=goal)return false;
        int tip=-1;for(int x:trail)if(occupied[x]&&degrees[x]==1){tip=x;break;}
        if(tip<0)return false;
        int previous=-1,x=tip;vector<int> path;
        while(x>=0) {
            path.push_back(x);int next=-1;
            for(int a=0;a<9;a++) {
                int y=x^(1<<a);if(occupied[y]&&y!=previous){next=y;break;}
            }
            previous=x;x=next;
        }
        if((int)path.size()!=goal+1)return false;
        answer=path;return true;
    }
    bool append(int remaining) {
        if(edgeCount+2*remaining<goal||edgeCount+remaining>goal)return false;
        if(!remaining)return finish();
        Bits attempted;
        int n=trail.size();
        for(int i=0;i<n;i++) {
            int v=trail[i];if(!occupied[v]||degrees[v]>=2)continue;
            for(int a=0;a<9;a++) {
                int y=v^(1<<a);if(occupied[y]||attempted[y])continue;
                attempted.set(y);
                if(degrees[y]>2)continue;
                bool valid=true;
                for(int j=0;j<9;j++){int z=y^(1<<j);if(occupied[z]&&degrees[z]>=2){valid=false;break;}}
                if(!valid)continue;
                toggle(y,true);trail.push_back(y);bool hit=append(remaining-1);trail.pop_back();toggle(y,false);
                if(hit)return true;
            }
        }
        return false;
    }
};
bool complete_forest(const vector<int>&basis,const vector<int>&points,int target,int tag) {
    array<int,512> inverse;inverse.fill(-1);
    for(int i=0;i<512;i++){int g=0;for(int a=0;a<9;a++)if(i&(1<<a))g^=basis[a];if(inverse[g]!=-1)abort();inverse[g]=i;}
    DirectFill f;f.goal=target;
    for(int x:points){int v=inverse[x];f.toggle(v,true);f.trail.push_back(v);}
    for(int x:f.trail)if(f.degrees[x]>2)return false;
    if(!f.append(target+1-points.size()))return false;
    cout<<"FOUND "<<tag<<" locked -1 basis";for(int g:basis)cout<<' '<<g;cout<<" path";for(int v:f.answer)cout<<' '<<v;cout<<endl;return true;
}
