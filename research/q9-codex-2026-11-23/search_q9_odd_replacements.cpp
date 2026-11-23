// Replace a selected vertex and search every clean 191-edge threading of the resulting set.
#define Q9_ALL_ORDERS_LIBRARY
#include "search_q9_odd_allorders.cpp"
int main(int argc,char**argv){
    if(argc!=3)return 2;int cap=stoi(argv[2]);Odd odd(argv[1],cap);
    uint64_t rows=0,configs=0,viable=0,orders=0,lifts=0,cuts=0;
    string line;
    while(getline(cin,line)){
        istringstream in(line);int v;Path side;while(in>>v)side.push_back(v);
        if(side.size()!=96||set<int>(side.begin(),side.end()).size()!=96)return 2;
        for(int x:side)if(x<0||x>=512||popcount(unsigned(x^side[0]))%2)return 2;
        Search s(side,1);Path pool;
        for(int y=0;y<512;y++)if(s.slot[y]<0&&popcount(unsigned(y^side[0]))%2==0)pool.push_back(y);
        for(int k=0;k<96;k++){
            int old=side[k];s.toggle(old,k,false);
            auto potential=[&](int x){int n=0;for(int d=0;d<9;d++)n+=popcount(unsigned(s.axes[x^(1<<d)]))<=2;return n;};
            int weak=0;bool dead=false;
            for(int x:side)if(x!=old){int options=potential(x);weak+=options<=1;if(!options||weak>1){dead=true;break;}}
            configs+=pool.size();
            if(!dead)for(int y:pool){
                int at=0;for(int d=0;d<9;d++)at+=popcount(unsigned(s.axes[y^(1<<d)]))<=1;
                if(!at||((at==1)&&weak))continue;
                s.toggle(y,k,true);int w=at==1;bool ok=true;
                for(int x:side)if(x!=old){int options=potential(x);w+=options<=1;if(!options||w>1){ok=false;break;}}
                s.toggle(y,k,false);
                if(!ok)continue;
                side[k]=y;Orders h(odd,side,cap);viable++;
                if(h.solve())return 0;
                side[k]=old;orders+=h.orders;lifts+=h.lifts;cuts+=h.cutoff;
            }
            s.toggle(old,k,true);
        }
        if(++rows%200==0)cout<<"AT "<<rows<<" "<<configs<<" "<<viable<<" "<<orders<<" "<<lifts<<" "<<cuts<<" "<<odd.novel.size()<<endl;
    }
    cout<<"DONE "<<rows<<" "<<configs<<" "<<viable<<" "<<orders<<" "<<lifts<<" "<<cuts<<" "<<odd.novel.size()<<endl;
}
