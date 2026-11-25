#include <array>
#include <vector>
#include <random>
#include <chrono>
#include <iostream>
#include <algorithm>
#include <csignal>
using namespace std;
using Word=unsigned long long;
using Bits=array<Word,8>;
constexpr int V=9,N=15,B=V+1,OUTPUT=B+N-1;
struct Gate{int op,a,b;};
using Circuit=array<Gate,N>;
using Values=array<Bits,B+N>;
mt19937 rng;
volatile sig_atomic_t stopFlag=0;
void stopped(int){stopFlag=1;}
array<Bits,B>inputs;
Bits target;
vector<pair<int,int>> edges={{0,1},{1,2},{2,3},{0,5},{1,6},{2,7},{3,8},{4,6},{6,8},{8,5},{5,7},{7,4}};
vector<int>covers;
Word operation(int op,Word a,Word b){return ((a^((op&1)?~0ULL:0))&(b^((op&2)?~0ULL:0)))^((op&4)?~0ULL:0);}
Values values(const Circuit&c){Values w;for(int i=0;i<B;i++)w[i]=inputs[i];for(int i=0;i<N;i++){auto g=c[i];for(int k=0;k<8;k++)w[B+i][k]=operation(g.op,w[g.a][k],w[g.b][k]);}return w;}
int score(const Circuit&c){auto w=values(c);int err=0;for(int k=0;k<8;k++){Word bad=w[OUTPUT][k]^target[k];err+=__builtin_popcountll(bad)+7*__builtin_popcountll(bad&~target[k]);}return err;}
Bits forceOutput(const Circuit&c,Values w,int i,Word v){w[B+i].fill(v);for(int j=i+1;j<N;j++){auto g=c[j];for(int k=0;k<8;k++)w[B+j][k]=operation(g.op,w[g.a][k],w[g.b][k]);}return w[OUTPUT];}
int coordinate(Circuit&c,int i,int temp){auto w=values(c);Bits f0=forceOutput(c,w,i,0),f1=forceOutput(c,w,i,~0ULL),care,want;for(int k=0;k<8;k++){care[k]=f0[k]^f1[k];want[k]=target[k]^f0[k];}int best=100000,count=0;Gate keep=c[i];
 for(int op=0;op<8;op++)for(int a=0;a<B+i;a++)for(int b=0;b<=a;b++){int err=0;for(int k=0;k<8;k++){Word bad=(operation(op,w[a][k],w[b][k])^want[k])&care[k];err+=__builtin_popcountll(bad)+7*__builtin_popcountll(bad&~target[k]);}int sc=err+(temp?int(rng()%(temp+1)):0);if(sc<best){best=sc;count=1;keep={op,a,b};}else if(sc==best&&rng()%++count==0)keep={op,a,b};}c[i]=keep;return score(c);}
Circuit seed(){int cover=covers[rng()%covers.size()];array<vector<int>,V>star;int lost=rng()%edges.size(),ei=0;for(auto[a,b]:edges){if(ei++==lost)continue;if((cover>>a&1)&&(cover>>b&1)){if(rng()%2)swap(a,b);}else if(!(cover>>a&1))swap(a,b);star[a].push_back(b);}vector<int>centers;for(int v=0;v<V;v++)if(!star[v].empty())centers.push_back(v);shuffle(centers.begin(),centers.end(),rng);vector<Gate>g;vector<int>roots;for(int v:centers){shuffle(star[v].begin(),star[v].end(),rng);int cur=star[v][0];for(size_t j=1;j<star[v].size();j++){g.push_back({7,cur,star[v][j]});cur=B+g.size()-1;}g.push_back({0,v,cur});roots.push_back(B+g.size()-1);}shuffle(roots.begin(),roots.end(),rng);int cur=roots[0];for(size_t j=1;j<roots.size();j++){g.push_back({7,cur,roots[j]});cur=B+g.size()-1;}if(g.size()!=N){cerr<<"FAULT seed size"<<endl;exit(2);}Circuit c;copy(g.begin(),g.end(),c.begin());return c;}
void reorder(Circuit&c){int i=rng()%(N-2);auto h=c[i+1];if(h.a==B+i||h.b==B+i)return;swap(c[i],c[i+1]);for(int j=i+2;j<N;j++)for(int*p:{&c[j].a,&c[j].b}){if(*p==B+i)++*p;else if(*p==B+i+1)--*p;}}
void show(const Circuit&c,int s,long long trial){cout<<"best "<<s<<" trial "<<trial<<" gates [";for(auto g:c)cout<<"("<<g.op<<","<<g.a<<","<<g.b<<"),";cout<<"]"<<endl;}
struct PhaseResult{int count;unsigned phase;array<bool,B+N>live;int binary;};
PhaseResult phaseOpt(const Circuit&c){array<bool,B+N>live{};live[OUTPUT]=true;int binary=0;for(int i=N-1;i>=0;i--)if(live[B+i]){binary++;live[c[i].a]=true;live[c[i].b]=true;}int best=100;unsigned keep=0;
 for(unsigned p=0;p<(1u<<N);p++){unsigned bad=(p>>(N-1)&1)?(1u<<OUTPUT):0;for(int i=0;i<N;i++)if(live[B+i]){auto g=c[i];int out=(p>>i&1)^(g.op>>2&1);int pa=g.a<B?0:(p>>(g.a-B)&1),pb=g.b<B?0:(p>>(g.b-B)&1);if((g.op&1)^pa^out)bad|=1u<<g.a;if((g.op>>1&1)^pb^out)bad|=1u<<g.b;}int z=__builtin_popcount(bad);if(z<best){best=z;keep=p;if(best==0)break;}}
 return {best,keep,live,binary};}
void realize(const Circuit&c,const PhaseResult&r){array<int,B+N>pos,neg;pos.fill(-1);neg.fill(-1);for(int i=0;i<V;i++)pos[i]=i;pos[V]=100000;vector<Gate>out;auto add=[&](int op,int a,int b){int ix=V+out.size();out.push_back({op,a,b});return ix;};auto complement=[&](int s){if(neg[s]<0)neg[s]=add(2,pos[s],pos[s]);return neg[s];};for(int i=0;i<N;i++)if(r.live[B+i]){auto g=c[i];int base=(r.phase>>i&1)^(g.op>>2&1);int pa=g.a<B?0:(r.phase>>(g.a-B)&1),pb=g.b<B?0:(r.phase>>(g.b-B)&1);int a=((g.op&1)^pa^base)?complement(g.a):pos[g.a];int b=((g.op>>1&1)^pb^base)?complement(g.b):pos[g.b];pos[B+i]=add(base,a,b);}int output=(r.phase>>(N-1)&1)?complement(OUTPUT):pos[OUTPUT];if(r.count==0)add(2,100000,100000);cout<<"REALIZATION {\"inputs\":"<<V<<",\"output\":"<<output<<",\"gates\":[";for(size_t i=0;i<out.size();i++){if(i)cout<<",";auto g=out[i];cout<<"["<<g.op<<","<<g.a<<","<<g.b<<"]";}cout<<"]}"<<endl;}
int main(int argc,char**argv){signal(SIGINT,stopped);signal(SIGTERM,stopped);rng.seed(argc>1?stoul(argv[1]):259209);int secs=argc>2?stoi(argv[2]):1500;for(int x=0;x<(1<<V);x++){for(int j=0;j<V;j++)if(x>>j&1)inputs[j][x/64]|=1ULL<<(x%64);for(auto[a,b]:edges)if((x>>a&1)&&(x>>b&1)){target[x/64]|=1ULL<<(x%64);break;}}for(int c=0;c<(1<<V);c++)if(__builtin_popcount((unsigned)c)==5){bool yes=true;for(auto[a,b]:edges)if(!(c>>a&1)&&!(c>>b&1))yes=false;if(yes)covers.push_back(c);}auto start=chrono::steady_clock::now();int global=100000,minnot=100;long long trial=0;vector<Circuit>archive;
 for(int run=0;;run++){Circuit c=seed(),local=c;if(!archive.empty()&&rng()%2)c=archive[rng()%archive.size()];int s=score(c),loc=s;local=c;for(int iter=0;iter<6000;iter++,trial++){if(trial%1000==0&&(stopFlag||chrono::duration<double>(chrono::steady_clock::now()-start).count()>secs)){cout<<"done "<<trial<<" best "<<global<<" minnot "<<minnot<<endl;return 0;}int temp=(iter%400<250)?0:(iter%400<350?8:24);s=coordinate(c,rng()%N,temp);if(iter%10==0){for(int j=0;j<10;j++)reorder(c);if(score(c)!=s){cerr<<"FAULT reorder"<<endl;return 2;}}if(s<loc){local=c;loc=s;}if(s<global){global=s;show(c,s,trial);}if(s==0&&(minnot==100||trial%1000==0)){auto r=phaseOpt(c);if(r.count<minnot){minnot=r.count;cout<<"EXACT binary "<<r.binary<<" NOT "<<r.count<<" phase "<<r.phase<<" trial "<<trial<<endl;show(c,s,trial);realize(c,r);}if(r.binary+max(1,r.count)<=16){cout<<"WITNESS"<<endl;return 0;}if(archive.size()<32)archive.push_back(c);else archive[rng()%archive.size()]=c;}if(iter%400==399){c=local;s=loc;}}}
}
