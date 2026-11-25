#include <algorithm>
#include <bit>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <random>
#include <vector>
using namespace std;using T=__uint128_t;using U=uint64_t;
struct Gate{int op,a,b;};
int main(int argc,char**argv){
 int seconds=argc>1?stoi(argv[1]):180;mt19937_64 rng(argc>2?stoull(argv[2]):75);const int n=7,K=18;
 vector<pair<int,int>> es;for(int a=0;a<n;a++)for(int b=a+1;b<n;b++)es.push_back({a,b});
 T inp[n],pairtable[21],singletons=0;for(int a=0;a<n;a++){inp[a]=0;for(int s=0;s<128;s++)if(s>>a&1)inp[a]|=T(1)<<s;singletons|=T(1)<<(1<<a);}
 for(int e=0;e<21;e++)pairtable[e]=inp[es[e].first]&inp[es[e].second];
 vector<int>bound(1<<21,-2);bound[0]=-1;int graphsSeen=0;U trials=0,signals=0,quadratic=0,admissible=0,near=0;auto start=chrono::steady_clock::now();
 auto getbound=[&](int E){int &v=bound[E];if(v!=-2)return v;unsigned adj[n]={};int m=popcount((unsigned)E);for(int e=0;e<21;e++)if(E>>e&1){auto[a,b]=es[e];adj[a]|=1U<<b;adj[b]|=1U<<a;}for(int a=0;a<n;a++)for(int b=a+1;b<n;b++){int co=popcount(adj[a]&adj[b]);if(co>1||((adj[a]>>b&1)&&co)){v=-1;return v;}}int alpha=0;for(int s=0;s<128;s++){bool ok=1;for(int a=0;a<n;a++)if((s>>a&1)&&(adj[a]&s)){ok=0;break;}if(ok)alpha=max(alpha,popcount((unsigned)s));}v=m+n-alpha-1;graphsSeen++;return v;};
 while(chrono::duration<double>(chrono::steady_clock::now()-start).count()<seconds){
  T val[n+K];U con[n+K]={};Gate gates[K];for(int a=0;a<n;a++)val[a]=inp[a];U ands=0;
  for(int j=0;j<K;j++){
   int a=rng()%(n+j),b=rng()%(n+j),op=rng()%2;T x=op?(val[a]|val[b]):(val[a]&val[b]);bool duplicate=!x||x==~T(0);for(int q=0;q<n+j&&!duplicate;q++)if(val[q]==x)duplicate=1;
   if(duplicate){if(j>0&&rng()%10==0)break;--j;continue;}
   gates[j]={op,a,b};val[n+j]=x;con[n+j]=con[a]|con[b]|(U(1)<<j);if(!op)ands|=U(1)<<j;signals++;
   if(x&singletons)continue;
   int E=0;T want=0;for(int e=0;e<21;e++){auto[u,v]=es[e];if((x>>((1<<u)|(1<<v)))&1){E|=1<<e;want|=pairtable[e];}}
   if(x!=want)continue;quadratic++;int B=getbound(E);if(B<0)continue;admissible++;int cost=popcount(con[n+j]);if(cost>B)continue;near++;
   bool bad=0;int badj=-1;for(int k=0;k<=j;k++)if((con[n+j]>>k&1)&&gates[k].op){T pure=0;int count=0;for(int a=0;a<n;a++)if((val[n+k]>>(1<<a))&1){pure|=inp[a];count++;}if(count<2||pure!=val[n+k])continue;int uses=0;for(int z=k+1;z<=j;z++)if((con[n+j]>>z&1)&&(gates[z].a==n+k||gates[z].b==n+k))uses++;if(uses>=2){bad=1;badj=k;break;}}
   if(cost<B||bad){cout<<"FOUND COST "<<cost<<" BOUND "<<B<<" SHARED_OR "<<bad<<" SHARED_GATE "<<badj<<" EDGEMASK "<<E<<" OUT "<<n+j<<" CONE "<<con[n+j]<<"\n";for(int e=0;e<21;e++)if(E>>e&1)cout<<"EDGE "<<es[e].first<<" "<<es[e].second<<"\n";for(int k=0;k<=j;k++)cout<<k<<" "<<(gates[k].op?"or":"and")<<" "<<gates[k].a<<" "<<gates[k].b<<"\n";cout.flush();return 0;}
  }
  trials++;
 }
 cout<<"DONE TRIALS "<<trials<<" SIGNALS "<<signals<<" QUADRATIC "<<quadratic<<" ADMISSIBLE "<<admissible<<" NEAR "<<near<<" GRAPHS "<<graphsSeen<<" SECONDS "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<"\n";
}
