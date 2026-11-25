#include <array>
#include <vector>
#include <random>
#include <chrono>
#include <iostream>
#include <algorithm>
#include <csignal>
using namespace std;
using Word=unsigned long long;
constexpr int V=10,MAX=64;
struct Gate{int op,a,b;};
using Circuit=vector<Gate>;
using Values=array<Word,MAX>;
mt19937 rng;
volatile sig_atomic_t stopFlag=0;
void stopped(int){stopFlag=1;}
array<Word,V>inputs;
Word target=0;
vector<pair<int,int>>edges;
vector<int>rows;
vector<int>covers;
int N,elastic;
array<bool,MAX> cone(const Circuit&c){array<bool,MAX>used{};used[V+N-1]=true;for(int i=N-1;i>=0;i--)if(used[V+i]){used[c[i].a]=true;used[c[i].b]=true;}return used;}
int cost(const Circuit&c){auto used=cone(c);int n=0;for(int i=0;i<N;i++)n+=used[V+i];return n;}
Values values(const Circuit&c){Values w{};for(int i=0;i<V;i++)w[i]=inputs[i];for(int i=0;i<N;i++){auto g=c[i];w[V+i]=g.op?(w[g.a]|w[g.b]):(w[g.a]&w[g.b]);}return w;}
int error(Word value){Word bad=value^target;return __builtin_popcountll(bad)+(elastic?0:3*__builtin_popcountll(bad&~target));}
int score(const Circuit&c){auto w=values(c);int e=error(w[V+N-1]);return elastic?e*128+cost(c):e;}
Word forceOutput(const Circuit&c,Values w,int i,Word v){w[V+i]=v;for(int j=i+1;j<N;j++){auto g=c[j];w[V+j]=g.op?(w[g.a]|w[g.b]):(w[g.a]&w[g.b]);}return w[V+N-1];}
int coordinate(Circuit&c,int i,int temp){auto live=cone(c);if(!live[V+i]){c[i]={int(rng()%2),int(rng()%(V+i)),int(rng()%(V+i))};return score(c);}auto w=values(c);Word f0=forceOutput(c,w,i,0),f1=forceOutput(c,w,i,~0ULL),care=f0^f1,want=target^f0;int best=100000,count=0;Gate keep=c[i];
 for(int op=0;op<2;op++)for(int a=0;a<V+i;a++)for(int b=0;b<=a;b++){Word value=op?(w[a]|w[b]):(w[a]&w[b]);Word bad=(value^want)&care;int err=__builtin_popcountll(bad)+(elastic?0:3*__builtin_popcountll(bad&~target));Gate old=c[i];c[i]={op,a,b};int sc=elastic?err*128+cost(c):err;c[i]=old;if(temp)sc+=rng()%(temp+1);if(sc<best){best=sc;count=1;keep={op,a,b};}else if(sc==best&&rng()%++count==0)keep={op,a,b};}c[i]=keep;return score(c);}
int resubstitute(Circuit&c){auto live=cone(c);vector<pair<int,int>>pairs;for(int j=0;j<N-1;j++)if(!live[V+j])for(int i=j+1;i<N;i++)if(live[V+i])pairs.push_back({j,i});if(pairs.empty())return score(c);auto[j,i]=pairs[rng()%pairs.size()];auto w=values(c);Word f0=forceOutput(c,w,i,0),f1=forceOutput(c,w,i,~0ULL),care=f0^f1,want=target^f0;int best=elastic?cost(c):100000,count=elastic?1:0;Gate keepJ=c[j],keepI=c[i];
 for(int op=0;op<2;op++)for(int a=0;a<V+j;a++)for(int b=0;b<=a;b++){Word h=op?(w[a]|w[b]):(w[a]&w[b]);for(int op2=0;op2<2;op2++)for(int d=0;d<V+j;d++){Word value=op2?(h|w[d]):(h&w[d]);Word bad=(value^want)&care;if(elastic&&bad)continue;int err=__builtin_popcountll(bad)+(elastic?0:3*__builtin_popcountll(bad&~target));c[j]={op,a,b};c[i]={op2,V+j,d};int sc=elastic?cost(c):err+int(rng()%4);if(sc<best){best=sc;count=1;keepJ=c[j];keepI=c[i];}else if(sc==best&&rng()%++count==0){keepJ=c[j];keepI=c[i];}}}c[j]=keepJ;c[i]=keepI;return score(c);}
Circuit seed(){array<vector<int>,V>star;int cover=covers[rng()%covers.size()],lost=elastic?-1:int(rng()%edges.size()),ei=0;for(auto[a,b]:edges){if(ei++==lost)continue;if((cover>>a&1)&&(cover>>b&1)){if(rng()%2)swap(a,b);}else if(!(cover>>a&1))swap(a,b);star[a].push_back(b);}vector<int>centers;for(int i=0;i<V;i++)if(!star[i].empty())centers.push_back(i);shuffle(centers.begin(),centers.end(),rng);Circuit c;vector<int>roots;for(int v:centers){shuffle(star[v].begin(),star[v].end(),rng);int cur=star[v][0];for(size_t j=1;j<star[v].size();j++){c.push_back({1,cur,star[v][j]});cur=V+c.size()-1;}c.push_back({0,v,cur});roots.push_back(V+c.size()-1);}while(roots.size()>1){shuffle(roots.begin(),roots.end(),rng);int a=roots.back();roots.pop_back();int b=roots.back();roots.pop_back();c.push_back({1,a,b});roots.push_back(V+c.size()-1);}while(int(c.size())<N){int pos=rng()%c.size();for(size_t j=pos;j<c.size();j++)for(int*p:{&c[j].a,&c[j].b})if(*p>=V+pos)++*p;c.insert(c.begin()+pos,{int(rng()%2),int(rng()%(V+pos)),int(rng()%(V+pos))});}if(int(c.size())!=N){cerr<<"FAULT seed size "<<c.size()<<endl;exit(2);}return c;}
void reorder(Circuit&c){int i=rng()%(N-2);auto g=c[i+1];if(g.a==V+i||g.b==V+i)return;swap(c[i],c[i+1]);for(int j=i+2;j<N;j++)for(int*p:{&c[j].a,&c[j].b}){if(*p==V+i)++*p;else if(*p==V+i+1)--*p;}}
void show(const Circuit&c,int s,long long trial){cout<<"best "<<s<<" trial "<<trial<<" gates [";for(auto g:c)cout<<"("<<g.op<<","<<g.a<<","<<g.b<<"),";cout<<"]"<<endl;}
void witness(const Circuit&c){auto live=cone(c);array<int,MAX>map;map.fill(-1);for(int i=0;i<V;i++)map[i]=i;Circuit out;for(int i=0;i<N;i++)if(live[V+i]){auto g=c[i];map[V+i]=V+out.size();out.push_back({g.op,map[g.a],map[g.b]});}cout<<"WITNESS {\"inputs\":10,\"output\":"<<map[V+N-1]<<",\"gates\":[";for(size_t i=0;i<out.size();i++){if(i)cout<<",";auto g=out[i];cout<<"["<<g.op<<","<<g.a<<","<<g.b<<"]";}cout<<"]}"<<endl;}
int main(int argc,char**argv){signal(SIGINT,stopped);signal(SIGTERM,stopped);rng.seed(argc>1?stoul(argv[1]):258301);int secs=argc>2?stoi(argv[2]):1200;elastic=argc>3?stoi(argv[3]):1;N=elastic?24:19;
 edges={{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}};
 for(auto[a,b]:edges){rows.push_back((1<<a)|(1<<b));target|=1ULL<<(rows.size()-1);}
 for(int mask=0;mask<1024;mask++){bool independent=true;for(auto[a,b]:edges)if((mask>>a&1)&&(mask>>b&1))independent=false;if(independent){bool maximal=true;for(int v=0;v<V;v++)if(!(mask>>v&1)){bool neighbor=false;for(auto[a,b]:edges)if((a==v&&(mask>>b&1))||(b==v&&(mask>>a&1)))neighbor=true;if(!neighbor)maximal=false;}if(maximal)rows.push_back(mask);}if(__builtin_popcount((unsigned)mask)==6){bool cover=true;for(auto[a,b]:edges)if(!(mask>>a&1)&&!(mask>>b&1))cover=false;if(cover)covers.push_back(mask);}}
 if(rows.size()!=30||covers.size()!=5){cerr<<"FAULT specification"<<endl;return 2;}for(size_t r=0;r<rows.size();r++)for(int i=0;i<V;i++)if(rows[r]>>i&1)inputs[i]|=1ULL<<r;
 auto start=chrono::steady_clock::now();long long trial=0;int global=100000;vector<Circuit>archive;
 for(int run=0;;run++){Circuit c=seed(),local=c;if(!elastic&&rng()%4==0)for(int i=0;i<N;i++)c[i]={int(rng()%2),int(rng()%(V+i)),int(rng()%(V+i))};if(!elastic&&!archive.empty()&&rng()%2)c=archive[rng()%archive.size()];int s=score(c),loc=s;local=c;if(s<global){global=s;show(c,s,trial);}for(int iter=0;iter<12000;iter++,trial++){if(trial%1000==0&&(stopFlag||chrono::duration<double>(chrono::steady_clock::now()-start).count()>secs)){cout<<"done "<<trial<<" best "<<global<<endl;return 0;}int temp=elastic?((iter%2000<1000)?2:(iter%2000<1500?6:16)):((iter%400<250)?0:(iter%400<350?8:32));s=coordinate(c,rng()%N,temp);if(iter%100==0)s=resubstitute(c);if(elastic&&s>=128){cerr<<"FAULT lost correctness"<<endl;return 2;}if(iter%10==0){for(int j=0;j<20;j++)reorder(c);if(score(c)!=s){cerr<<"FAULT reorder"<<endl;return 2;}}if(s<loc){loc=s;local=c;}if(s<global){global=s;show(c,s,trial);}if((elastic&&s<=19)||(!elastic&&s==0)){witness(c);return 0;}if(!elastic&&s<=global&&rng()%100==0){if(archive.size()<32)archive.push_back(c);else archive[rng()%archive.size()]=c;}if(!elastic&&iter%400==399){c=local;s=loc;}}}
}
