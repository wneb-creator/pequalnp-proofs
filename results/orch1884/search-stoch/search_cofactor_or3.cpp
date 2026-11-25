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
constexpr int V=9,B=10,N=14,OUT=B+N-1;
struct Gate {int op,a,b;};
using Circuit=array<Gate,N>;
using Values=array<Bits,B+N>;
mt19937 rng;
volatile sig_atomic_t stopped=0;
void stop(int){stopped=1;}
array<Bits,B> inputs{};
Bits target{};
vector<pair<int,int>> edges={{0,1},{1,2},{2,3},{0,5},{1,6},{2,7},{3,8},{4,6},{6,8},{8,5},{5,7},{7,4}};
vector<int> covers;
Word apply(int op,Word a,Word b){return op==0?(a&b):(a|b);}
Values values(const Circuit&c){Values w{};for(int i=0;i<B;i++)w[i]=inputs[i];for(int i=0;i<N;i++){auto g=c[i];for(int k=0;k<8;k++)w[B+i][k]=apply(g.op,w[g.a][k],w[g.b][k]);}return w;}
int score(const Circuit&c){auto w=values(c);int s=0;for(int k=0;k<8;k++){Word bad=w[OUT][k]^target[k];s+=__builtin_popcountll(bad)+3*__builtin_popcountll(bad&~target[k]);}return s;}
Bits forced(const Circuit&c,Values w,int i,Word bit){w[B+i].fill(bit);for(int j=i+1;j<N;j++){auto g=c[j];for(int k=0;k<8;k++)w[B+j][k]=apply(g.op,w[g.a][k],w[g.b][k]);}return w[OUT];}
int coordinate(Circuit&c,int i,int temperature){
 auto w=values(c);Bits f0=forced(c,w,i,0),f1=forced(c,w,i,~0ULL),care{},want{};
 for(int k=0;k<8;k++){care[k]=f0[k]^f1[k];want[k]=target[k]^f0[k];}
 int best=1000000,ties=0;Gate keep=c[i];
 for(int op=0;op<2;op++)for(int a=0;a<B+i;a++)for(int b=0;b<=a;b++){
  int s=0;for(int k=0;k<8;k++){Word bad=(apply(op,w[a][k],w[b][k])^want[k])&care[k];s+=__builtin_popcountll(bad)+3*__builtin_popcountll(bad&~target[k]);}
  if(temperature)s+=rng()%(temperature+1);
  if(s<best){best=s;ties=1;keep={op,a,b};}else if(s==best&&rng()%++ties==0)keep={op,a,b};
 }
 c[i]=keep;return score(c);
}
Circuit seed(){
 int cover=covers[rng()%covers.size()];array<vector<int>,V>stars;
 int drop1=rng()%edges.size(),drop2=rng()%(edges.size()-1);if(drop2>=drop1)drop2++;
 for(int i=0;i<int(edges.size());i++)if(i!=drop1&&i!=drop2){auto[a,b]=edges[i];if((cover>>a&1)&&(cover>>b&1)){if(rng()%2)swap(a,b);}else if(!(cover>>a&1))swap(a,b);stars[a].push_back(b);}
 vector<int>centers;for(int v=0;v<V;v++)if(!stars[v].empty())centers.push_back(v);shuffle(centers.begin(),centers.end(),rng);
 vector<Gate>g;vector<int>roots;
 for(int v:centers){shuffle(stars[v].begin(),stars[v].end(),rng);int cur=stars[v][0];for(size_t i=1;i<stars[v].size();i++){g.push_back({1,cur,stars[v][i]});cur=B+g.size()-1;}g.push_back({0,v,cur});roots.push_back(B+g.size()-1);}
 shuffle(roots.begin(),roots.end(),rng);int cur=roots[0];for(size_t i=1;i<roots.size();i++){g.push_back({1,cur,roots[i]});cur=B+g.size()-1;}
 if(g.size()>N){cerr<<"FAULT seed size"<<endl;exit(2);}while(g.size()<N){int last=B+g.size()-1;g.push_back({0,last,last});}
 Circuit c;copy(g.begin(),g.end(),c.begin());
 if(rng()%2){int i=rng()%N;if(rng()%2)c[i].a=9;else c[i].b=9;}
 return c;
}
void reorder(Circuit&c){int i=rng()%(N-2);auto h=c[i+1];if(h.a==B+i||h.b==B+i)return;swap(c[i],c[i+1]);for(int j=i+2;j<N;j++)for(int*p:{&c[j].a,&c[j].b}){if(*p==B+i)++*p;else if(*p==B+i+1)--*p;}}
void show(const Circuit&c,int s,long long trial){cout<<"best "<<s<<" trial "<<trial<<" gates [";for(auto g:c)cout<<"("<<g.op<<","<<g.a<<","<<g.b<<"),";cout<<"]"<<endl;}
void witness(const Circuit&c){
 for(int x=0;x<512;x++){array<bool,B+N>w{};for(int i=0;i<V;i++)w[i]=x>>i&1;w[9]=w[0]||w[3]||w[4];for(int i=0;i<N;i++){auto g=c[i];if(g.op<0||g.op>1||g.a<0||g.b<0||g.a>=B+i||g.b>=B+i){cerr<<"FAULT witness indices"<<endl;exit(2);}w[B+i]=g.op==0?w[g.a]&&w[g.b]:w[g.a]||w[g.b];}bool want=false;for(auto[a,b]:edges)want|=(x>>a&1)&&(x>>b&1);if(w[OUT]!=want){cerr<<"FAULT scalar witness"<<endl;exit(2);}}
 cout<<"COFACTOR_WITNESS {\"inputs\":10,\"output\":"<<OUT<<",\"free_or\":[0,3,4],\"gates\":[";for(int i=0;i<N;i++){if(i)cout<<",";auto g=c[i];cout<<"["<<g.op<<","<<g.a<<","<<g.b<<"]";}cout<<"]}"<<endl;
 vector<Gate>full={{1,1,4},{1,11,5}};
 auto remap=[](int i){return i<9?i+1:i==9?12:i+3;};
 for(auto g:c)full.push_back({g.op,remap(g.a),remap(g.b)});
 full.push_back({0,0,12});full.push_back({1,OUT+3,27});
 vector<pair<int,int>>original={{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}};
 for(int x=0;x<1024;x++){array<bool,29>w{};for(int i=0;i<10;i++)w[i]=x>>i&1;w[10]=!w[0];for(int i=0;i<18;i++){auto g=full[i];if(g.a>=11+i||g.b>=11+i){cerr<<"FAULT lift indices"<<endl;exit(2);}w[11+i]=g.op==0?w[g.a]&&w[g.b]:w[g.a]||w[g.b];}bool want=false;for(auto[a,b]:original)want|=(x>>a&1)&&(x>>b&1);if(w[28]!=want){cerr<<"FAULT lift truth"<<endl;exit(2);}}
 cout<<"FULL_WITNESS {\"inputs\":11,\"output\":28,\"gates\":[";for(int i=0;i<18;i++){if(i)cout<<",";auto g=full[i];cout<<"["<<g.op<<","<<g.a<<","<<g.b<<"]";}cout<<"]}"<<endl;
}
void setup(){
 for(int x=0;x<512;x++){for(int i=0;i<V;i++)if(x>>i&1)inputs[i][x/64]|=1ULL<<(x%64);for(auto[a,b]:edges)if((x>>a&1)&&(x>>b&1)){target[x/64]|=1ULL<<(x%64);break;}}
 for(int k=0;k<8;k++)inputs[9][k]=inputs[0][k]|inputs[3][k]|inputs[4][k];
 for(int c=0;c<512;c++)if(__builtin_popcount((unsigned)c)==5){bool ok=true;for(auto[a,b]:edges)if(!(c>>a&1)&&!(c>>b&1))ok=false;if(ok)covers.push_back(c);}
}
int main(int argc,char**argv){
 setup();signal(SIGINT,stop);signal(SIGTERM,stop);rng.seed(argc>1?stoul(argv[1]):188501);int seconds=argc>2?stoi(argv[2]):1200;
 auto start=chrono::steady_clock::now();int global=100000;long long trial=0;vector<Circuit>archive;
 for(int run=0;;run++){
  Circuit c=seed();if(!archive.empty()&&rng()%2)c=archive[rng()%archive.size()];int s=score(c),localScore=s;Circuit local=c;
  for(int i=0;i<6000;i++,trial++){
   if(trial%1000==0&&(stopped||chrono::duration<double>(chrono::steady_clock::now()-start).count()>seconds)){cout<<"done "<<trial<<" best "<<global<<endl;return 0;}
   int temp=i%400<250?0:i%400<350?12:48;s=coordinate(c,rng()%N,temp);
   if(i%10==0){for(int j=0;j<10;j++)reorder(c);if(score(c)!=s){cerr<<"FAULT reorder"<<endl;return 2;}}
   if(s<localScore){local=c;localScore=s;}if(s<global){global=s;show(c,s,trial);}
   if(s==0){witness(c);return 0;}
   if(s<=global+4&&rng()%100==0){if(archive.size()<32)archive.push_back(c);else archive[rng()%archive.size()]=c;}
   if(i%400==399){c=local;s=localScore;}
  }
 }
}
