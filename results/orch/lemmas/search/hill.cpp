#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <random>
#include <vector>
using U=__uint128_t;
struct G {int op,a,b;};
std::mt19937_64 rng(184);
int n=13,notmode=0;
U inputs[7],target;
int pc(U x){return __builtin_popcountll((unsigned long long)x)+__builtin_popcountll((unsigned long long)(x>>64));}
int score(const std::vector<G>&g){U w[64];for(int i=0;i<7;i++)w[i]=inputs[i];for(int i=0;i<n;i++) {auto v=g[i];w[7+i]=v.op==0?w[v.a]&w[v.b]:v.op==1?w[v.a]|w[v.b]:~w[v.a];}return pc(w[6+n]^target);}
void dump(const std::vector<G>&g){for(int i=0;i<n;i++)printf("(%d,%d,%d) ",g[i].op,g[i].a,g[i].b);puts("");fflush(stdout);}
std::vector<G> seed(){std::vector<G> orig={{1,0,2},{1,3,5},{1,7,8},{0,6,9},{1,1,5},{0,3,11},{1,0,1},{1,4,5},{0,13,14},{1,0,4},{0,2,16},{1,10,12},{1,15,17},{1,18,19}};if(n==14)return orig;int d=rng()%14;int subst=rng()%(7+d);std::vector<G> g;for(int i=0;i<14;i++){if(i==d)continue;auto v=orig[i];for(int *j:{&v.a,&v.b}){if(*j==7+d)*j=subst;if(*j>7+d)(*j)--;}g.push_back(v);}return g;}
int main(int argc,char**argv){if(argc>1)n=atoi(argv[1]);if(argc>2)notmode=atoi(argv[2]);int secs=argc>3?atoi(argv[3]):120;for(int i=0;i<7;i++){inputs[i]=0;for(int j=0;j<128;j++)if((j>>i)&1)inputs[i]|=U(1)<<j;}target=0;int es[][2]={{0,2},{1,3},{0,4},{1,4},{2,4},{0,5},{1,5},{3,5},{0,6},{2,6},{3,6},{5,6}};for(auto e:es)target|=inputs[e[0]]&inputs[e[1]];int best=999;long long it=0;auto start=std::chrono::steady_clock::now();for(int restart=0;;restart++){auto g=seed();int noti=-1;if(notmode){noti=rng()%n;g[noti].op=2;}int s=score(g);for(int local=0;local<200000;local++,it++){int i=rng()%n;auto old=g[i];int typ=rng()%4;if(typ==0){if(i!=noti)g[i].op^=1;}else if(typ==1)g[i].a=rng()%(7+i);else if(typ==2)g[i].b=rng()%(7+i);else{g[i].a=rng()%(7+i);g[i].b=rng()%(7+i);if(i!=noti)g[i].op=rng()%2;}int t=score(g);double temp=0.10+1.4*double(200000-local)/200000;if(t<=s || std::generate_canonical<double,53>(rng)<exp((s-t)/temp))s=t;else g[i]=old;if(s<best){best=s;printf("BEST %d restart %d iter %lld\n",best,restart,it);dump(g);}if(s==0)return 0;if(it%100000==0){double dur=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();if(dur>=secs){printf("DONE best %d iterations %lld seconds %.3f\n",best,it,dur);return 0;}}}}}
