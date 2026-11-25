#include <algorithm>
#include <bit>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <random>
#include <string>
#include <vector>
#include <chrono>
using namespace std;
using U=uint64_t;
struct Gate { int op,a,b; };
int main(int argc,char**argv){
 if(argc<4)return 2;
 ifstream in(argv[1]); int n,m;in>>n>>m; vector<pair<int,int>>edges(m);for(auto &[a,b]:edges)in>>a>>b;
 int seconds=stoi(argv[2]); mt19937_64 rng(stoull(argv[3]));
 vector<int> indeps,maxis,covers;int alpha=0;
 for(int s=0;s<(1<<n);s++){bool ok=1;for(auto[a,b]:edges)if((s>>a&1)&&(s>>b&1))ok=0;if(ok){indeps.push_back(s);alpha=max(alpha,popcount((unsigned)s));}}
 vector<char> isi(1<<n);for(int s:indeps)isi[s]=1;
 for(int s:indeps){bool maximal=1;for(int j=0;j<n;j++)if(!(s>>j&1)&&isi[s|(1<<j)])maximal=0;if(maximal)maxis.push_back(s);if(popcount((unsigned)s)==alpha)covers.push_back(((1<<n)-1)^s);}
 vector<int>rows;for(auto[a,b]:edges)rows.push_back((1<<a)|(1<<b));for(int s:maxis)rows.push_back(s);
 if(rows.size()>63)return 3;
 U mask=(U(1)<<rows.size())-1,target=(U(1)<<m)-1;vector<U>input(n);
 for(int j=0;j<n;j++)for(int r=0;r<(int)rows.size();r++)if(rows[r]>>j&1)input[j]|=U(1)<<r;
 bool profileGoal=argc>4;
 int full=m+n-alpha-1,K=full-(profileGoal?0:1);
 auto randint=[&](int k){return int(rng()%k);};
 auto make_seed=[&](){
  vector<Gate>gs;vector<vector<int>>groups(n);int cover=covers[randint(covers.size())];
  for(auto[a,b]:edges){if((cover>>a&1)&&(cover>>b&1)){if(randint(2))groups[a].push_back(b);else groups[b].push_back(a);}else if(cover>>a&1)groups[a].push_back(b);else groups[b].push_back(a);}
  auto combine=[&](vector<int>vs,int op){while(vs.size()>1){int i=randint(vs.size());int a=vs[i];vs.erase(vs.begin()+i);i=randint(vs.size());int b=vs[i];vs.erase(vs.begin()+i);gs.push_back({op,a,b});vs.push_back(n+gs.size()-1);}return vs[0];};
  vector<int>order(n);for(int i=0;i<n;i++)order[i]=i;shuffle(order.begin(),order.end(),rng);vector<int>outs;
  for(int c:order)if(!groups[c].empty()){int s=combine(groups[c],1);gs.push_back({0,c,s});outs.push_back(n+gs.size()-1);}
  combine(outs,1);
  if(profileGoal)return gs;
  int del=randint(gs.size()-1),replacement=randint(2)?gs[del].a:gs[del].b;
  vector<Gate>out;for(int i=0;i<(int)gs.size();i++)if(i!=del){Gate g=gs[i];auto remap=[&](int a){if(a==n+del)a=replacement;if(a>n+del)--a;return a;};g.a=remap(g.a);g.b=remap(g.b);out.push_back(g);}return out;
 };
 auto eval=[&](const vector<Gate>&gs){U vs[128];for(int i=0;i<n;i++)vs[i]=input[i];for(int i=0;i<(int)gs.size();i++)vs[n+i]=gs[i].op?(vs[gs[i].a]|vs[gs[i].b]):(vs[gs[i].a]&vs[gs[i].b]);return vs[n+gs.size()-1];};
 auto hasBad=[&](const vector<Gate>&gs){
  U vs[128],cones[128];for(int i=0;i<n;i++){vs[i]=input[i];cones[i]=0;}U ands=0;
  for(int i=0;i<(int)gs.size();i++){auto g=gs[i];vs[n+i]=g.op?(vs[g.a]|vs[g.b]):(vs[g.a]&vs[g.b]);cones[n+i]=cones[g.a]|cones[g.b];if(g.a>=n)cones[n+i]|=U(1)<<(g.a-n);if(g.b>=n)cones[n+i]|=U(1)<<(g.b-n);if(!g.op)ands|=U(1)<<i;}
  for(int i=0;i<(int)gs.size();i++)if(!gs[i].op){U lower=cones[n+i]&ands;U owned=vs[n+i]&target;for(int j=0;j<(int)gs.size();j++)if(lower>>j&1)owned&=~vs[n+j];if(owned){int common=(1<<n)-1;for(int e=0;e<m;e++)if(owned>>e&1)common&=(1<<edges[e].first)|(1<<edges[e].second);if(!common)return true;}}
  return false;
 };
 auto print=[&](const vector<Gate>&gs){for(int i=0;i<(int)gs.size();i++)cout<<i<<" "<<(gs[i].op?"or":"and")<<" "<<gs[i].a<<" "<<gs[i].b<<"\n";cout.flush();};
 auto start=chrono::steady_clock::now();long long iteration=0,restarts=0;int best=1000;vector<Gate>bestgs;double besttime=0;
 cout<<"N "<<n<<" M "<<m<<" ALPHA "<<alpha<<" ROWS "<<rows.size()<<" GATES "<<K<<"\n";cout.flush();
 while(chrono::duration<double>(chrono::steady_clock::now()-start).count()<seconds){
  auto gs=make_seed();if((int)gs.size()!=K)return 4;U out=eval(gs);double wp=(restarts%3==0?1.0:restarts%3==1?2.0:0.5);auto score=[&](U v){return wp*popcount(v&~target&mask)+popcount((~v)&target)+(profileGoal && v==target && !hasBad(gs)?0.1:0.0);};double current=score(out);++restarts;
  for(int local=0;local<200000;local++,iteration++){
   int bad=popcount(out^target);if(bad<best){best=bad;bestgs=gs;besttime=chrono::duration<double>(chrono::steady_clock::now()-start).count();cout<<"BEST "<<best<<" TIME "<<besttime<<" ITER "<<iteration<<" RESTART "<<restarts<<" FP "<<popcount(out&~target&mask)<<" FN "<<popcount((~out)&target)<<"\n";print(gs);}
   if(!bad && (!profileGoal || hasBad(gs))){cout<<"FOUND\n";print(gs);return 0;}
   int g1=randint(K),g2=randint(K);Gate old1=gs[g1],old2=gs[g2];
   auto mutate=[&](int j){int what=randint(10);if(what==0)gs[j].op^=1;else if(what<6)gs[j].a=randint(n+j);else gs[j].b=randint(n+j);};
   mutate(g1);bool doublem=randint(5)==0;if(doublem)mutate(g2);
   U nextout=eval(gs);double next=score(nextout);double T=0.02+1.25*pow(1.0-double(local)/200000,3);
   if(next<=current || double(rng()>>11)*0x1.0p-53<exp((current-next)/T)){out=nextout;current=next;}else {gs[g1]=old1;if(doublem)gs[g2]=old2;}
  }
 }
 cout<<"DONE BEST "<<best<<" ITER "<<iteration<<" RESTARTS "<<restarts<<" TIME "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<"\n";print(bestgs);
}
