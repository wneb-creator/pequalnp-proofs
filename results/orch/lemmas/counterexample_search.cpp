#include <array>
#include <algorithm>
#include <bit>
#include <chrono>
#include <cstdio>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <random>
#include <vector>

// Full-truth-table stochastic search, not an exhaustive certificate.
struct Gate { int op, a, b; };
using Circuit = std::array<Gate,19>;
using Table = std::array<uint64_t,16>;
std::array<Table,29> wire;
Table target, lowmask;
std::mt19937_64 rng;
bool requireActiveNot=false;
int exactNotCount=0;
bool rejectConstantReplacement=false;
int edges[15][2]={{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}};

int eval(const Circuit &c, int weight=0) {
    bool hasNot=false;int notCount=0;
    for(int i=0;i<19;i++) {
        const Gate &g=c[i]; hasNot |= g.op==2;notCount+=g.op==2;
        for(int k=0;k<16;k++) {
            auto a=wire[g.a][k],b=wire[g.b][k];
            wire[10+i][k]=g.op==0?(a&b):g.op==1?(a|b):~a;
        }
    }
    if(!hasNot) return 1000000;
    if(exactNotCount&&notCount!=exactNotCount)return 1000000;
    if(exactNotCount==1) {
        int ni=0;while(c[ni].op!=2)ni++;
        int input=c[ni].a;
        const int maximalIndependent[15]={50,69,104,116,138,201,208,276,385,402,521,548,554,770,773};
        bool trueOnIndependent=false,falseOnEdge=false;
        for(int a:maximalIndependent)trueOnIndependent|=(wire[input][a/64]>>(a%64))&1;
        for(auto &e:edges) {
            int a=(1<<e[0])|(1<<e[1]);
            falseOnEdge|=!((wire[input][a/64]>>(a%64))&1);
        }
        if(!trueOnIndependent||!falseOnEdge)return 1000000;
        if(rejectConstantReplacement) {
            Table actual=wire[28];
            for(int constant=0;constant<2;constant++) {
                for(int k=0;k<16;k++)wire[10+ni][k]=constant?~0ull:0ull;
                for(int j=ni+1;j<19;j++)for(int k=0;k<16;k++) {
                    const Gate &g=c[j];auto a=wire[g.a][k],b=wire[g.b][k];
                    wire[10+j][k]=g.op==0?(a&b):g.op==1?(a|b):~a;
                }
                bool same=wire[28]==actual;
                if(same){wire[28]=actual;return 1000000;}
            }
            wire[28]=actual;
        }
    }
    if(requireActiveNot) {
        bool used[29]={};used[28]=true;
        bool activeNot=false;
        for(int i=18;i>=0;i--) if(used[10+i]) {
            used[c[i].a]=true;
            if(c[i].op!=2)used[c[i].b]=true;
            activeNot|=c[i].op==2;
        }
        if(!activeNot)return 1000000;
    }
    int errors=0, lowerrors=0;
    for(int k=0;k<16;k++) {
        auto d=wire[28][k]^target[k];
        errors+=std::popcount(d);
        lowerrors+=std::popcount(d&lowmask[k]);
    }
    return errors+weight*lowerrors;
}

bool save(const Circuit &c,int score,int iteration,const std::string &path) {
    std::string temp=path+".new";
    std::ofstream out(temp);
    out<<"score "<<score<<" iteration "<<iteration<<"\n";
    for(int i=0;i<19;i++) out<<(i+10)<<" "<<(c[i].op==0?"and":c[i].op==1?"or":"not")<<" "<<c[i].a<<" "<<c[i].b<<"\n";
    out<<"errors:";
    eval(c);
    for(int a=0;a<1024;a++) if(((wire[28][a/64]^target[a/64])>>(a%64))&1) out<<" "<<a;
    out<<"\n";
    out.flush();
    if(!out.good())return false;
    out.close();
    return std::rename(temp.c_str(),path.c_str())==0;
}

Circuit seed() {
    static std::vector<int> covers;
    if(covers.empty())for(int m=0;m<1024;m++)if(std::popcount((unsigned)m)==6) {
        bool ok=true;for(auto &e:edges)ok&=((m>>e[0])&1)||((m>>e[1])&1);
        if(ok)covers.push_back(m);
    }
    int cv=covers[rng()%covers.size()];
    std::vector<int> stars;
    std::vector<int> adj[10];
    for(auto &e:edges) {
        int a=e[0],b=e[1];
        if(!((cv>>a)&1)||(((cv>>b)&1)&&(rng()%2)))std::swap(a,b);
        adj[a].push_back(b);
    }
    for(int i=0;i<10;i++)if(!adj[i].empty())stars.push_back(i);
    std::shuffle(stars.begin(),stars.end(),rng);
    std::vector<Gate> init;
    std::vector<int> out;
    auto combine=[&](std::vector<int> pool,int op) {
        while(pool.size()>1) {
            std::shuffle(pool.begin(),pool.end(),rng);
            int a=pool.back();pool.pop_back();int b=pool.back();pool.pop_back();
            init.push_back({op,a,b});pool.push_back(9+init.size());
        }
        return pool[0];
    };
    for(int a:stars) {
        int b=combine(adj[a],1);
        init.push_back({0,a,b});out.push_back(9+init.size());
    }
    combine(out,1);
    if(init.size()!=20)std::abort();
    int gone=rng()%20,subst=(rng()%2?init[gone].a:init[gone].b);
    Circuit c;
    for(int i=0,j=0;i<20;i++) if(i!=gone) {
        Gate g=init[i];
        auto remap=[&](int x) {if(x==gone+10)x=subst; if(x>gone+10)x--;return x;};
        g.a=remap(g.a);g.b=remap(g.b);c[j++]=g;
    }
    int neg=rng()%18;c[neg].op=2;
    for(int k=1;k<exactNotCount;k++) {
        do{neg=rng()%18;}while(c[neg].op==2);
        c[neg].op=2;
    }
    return c;
}

void mutate(Circuit &c,int count) {
    for(int k=0;k<count;k++) {
        int i=rng()%19,field=rng()%3;
        if(field==0) {
            int op=rng()%3;
            if(exactNotCount&&op==2&&c[i].op!=2) {
                int other;
                do{other=rng()%19;}while(c[other].op!=2);
                c[other].op=c[i].op;
            }
            else if(exactNotCount&&op!=2&&c[i].op==2) {
                int other;
                do{other=rng()%19;}while(c[other].op==2);
                c[other].op=2;
            }
            c[i].op=op;
        }
        else if(field==1)c[i].a=rng()%(10+i);
        else c[i].b=rng()%(10+i);
    }
}

int main(int argc,char**argv) {
    int seconds=argc>1?std::stoi(argv[1]):300;
    unsigned long seednum=argc>2?std::stoul(argv[2]):2592;
    std::string path=argc>3?argv[3]:"/tmp/oec/pequalnp-pilot-128/counterexample-best.txt";
    requireActiveNot=argc>4&&std::stoi(argv[4]);
    exactNotCount=argc>5?std::stoi(argv[5]):0;
    rejectConstantReplacement=argc>6&&std::stoi(argv[6]);
    rng.seed(seednum);
    for(int a=0;a<1024;a++) {
        for(int j=0;j<10;j++) if((a>>j)&1)wire[j][a/64]|=1ull<<(a%64);
        bool y=false;for(auto &e:edges)y|=((a>>e[0])&1)&&((a>>e[1])&1);
        if(y)target[a/64]|=1ull<<(a%64);
        if(std::popcount((unsigned)a)<=2)lowmask[a/64]|=1ull<<(a%64);
    }
    int best=1000000, it=0,stagnant=0,restarts=0;
    Circuit current=seed(); int weight=0,score=eval(current,weight);
    Circuit bestCircuit=current;
    auto started=std::chrono::steady_clock::now(), next=started;
    while(std::chrono::steady_clock::now()-started<std::chrono::seconds(seconds)) {
        Circuit trial=current;
        mutate(trial,1+(rng()%100<5)+(rng()%100<1)*2);
        int val=eval(trial,weight);it++;stagnant++;
        if(val<=score){current=trial;if(val<score)stagnant=0;score=val;}
        int err=eval(trial);
        if(err<best) {
            best=err;bestCircuit=trial;bool saved=save(trial,best,it,path);
            std::cout<<"best "<<best<<" iteration "<<it<<" restart "<<restarts<<std::endl;
            if(best==0&&saved)return 0;
        }
        if(stagnant>40000) {
            current=seed();weight=(rng()%3==0?8:0);score=eval(current,weight);stagnant=0;restarts++;
        }
        auto now=std::chrono::steady_clock::now();
        if(now>=next) {
            std::cout.clear();
            bool saved=save(bestCircuit,best,it,path);
            std::cout<<"elapsed "<<std::chrono::duration_cast<std::chrono::seconds>(now-started).count()<<" iterations "<<it<<" best "<<best<<" current "<<score<<" restarts "<<restarts<<std::endl;
            if(best==0&&saved)return 0;
            next=now+std::chrono::seconds(30);
        }
    }
    save(bestCircuit,best,it,path);
    std::cout<<"DONE no witness found; best errors "<<best<<" iterations "<<it<<" restarts "<<restarts<<std::endl;
    return 1;
}
