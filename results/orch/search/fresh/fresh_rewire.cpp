#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <map>
#include <random>
#include <set>
#include <stdexcept>
#include <vector>
using namespace std;
using Word=__uint128_t;
struct Gate{int a,b;bool isAnd;};
using Circuit=vector<Gate>;
using Wires=array<Word,96>;
struct Problem {
 int k,b,n,np,nt; vector<int> rows,assign; Wires raw{};Word target=0,mask=0;
 void read(){
  cin>>k>>b>>np>>nt;n=k+b;
  if(nt>=128||n+50>=96)throw runtime_error("instance capacity");
  rows.resize(k);for(int& v:rows)cin>>v;
  assign.resize(nt);for(int i=0;i<nt;i++){cin>>assign[i];for(int j=0;j<n;j++)if(assign[i]>>j&1)raw[j]|=Word(1)<<i;}
  target=(Word(1)<<np)-1;mask=(Word(1)<<nt)-1;
 }
} P;
mt19937 rng;
int pick(int n){return uniform_int_distribution<int>(0,n-1)(rng);}
int pc(Word x){return popcount((uint64_t)x)+popcount((uint64_t)(x>>64));}
Word ev(Gate g,const Wires& w){return g.isAnd?(w[g.a]&w[g.b]):(w[g.a]|w[g.b]);}
Wires eval(const Circuit& c){Wires w=P.raw;for(int j=0;j<(int)c.size();j++)w[P.n+j]=ev(c[j],w);return w;}
Word suffix(const Circuit& c,Wires w,int j,Word h){w[P.n+j]=h;for(int t=j+1;t<(int)c.size();++t)w[P.n+t]=ev(c[t],w);return w[P.n+c.size()-1];}
int gate(Circuit& c,int a,int b,bool op){if(a>b)swap(a,b);c.push_back({a,b,op});return P.n+c.size()-1;}
int join(Circuit& c,vector<int> v){shuffle(v.begin(),v.end(),rng);while(v.size()>1){int a=v.back();v.pop_back();int j=pick(v.size());v[j]=gate(c,a,v[j],false);}return v[0];}
Circuit seed(int omit){
 Circuit c;vector<int> stars,ps(P.k);for(int i=0;i<P.k;i++)ps[i]=i;shuffle(ps.begin(),ps.end(),rng);
 for(int i:ps){
  vector<int> ls;for(int v=P.k;v<P.n;v++)if(P.rows[i]>>v&1 && (omit<0||P.assign[omit]!=((1<<i)|(1<<v))))ls.push_back(v);
  int y=join(c,ls);stars.push_back(gate(c,i,y,true));
 }
 join(c,stars);return c;
}
void scrambleOrder(Circuit& c){
 const int m=c.size();vector<int>rename(P.n+m,-1),opts;for(int i=0;i<P.n;i++)rename[i]=i;Circuit out;
 while((int)out.size()<m){opts.clear();
  for(int j=0;j<m;j++)if(rename[P.n+j]<0&&rename[c[j].a]>=0&&rename[c[j].b]>=0&&(j<m-1||(int)out.size()==m-1))opts.push_back(j);
  int j=opts[pick(opts.size())];rename[P.n+j]=gate(out,rename[c[j].a],rename[c[j].b],c[j].isAnd);
 }
 c=out;
}
int weighted(Word dif,Word hot,Word hotter){return pc(dif)+pc(dif&hot)+pc(dif&hotter);}
struct Stats {uint64_t steps=0,proposals=0;int best=1000;set<pair<uint64_t,uint64_t>>single;};
bool step(Circuit& c,Word hot,Word hotter,int temp,Stats& st){
 int m=c.size();Wires w=eval(c);Word old=w[P.n+m-1]^P.target;
 if(!old)return true;
 Gate choice{};int chosen=-1,best=100000,ties=0;
 int trials=8+pick(9);
 for(int t=0;t<trials;t++){
  int j=pick(m),nw=P.n+j;
  Word lo=suffix(c,w,j,0),hi=suffix(c,w,j,P.mask),care=hi^lo;
  if(!care&&t+2<trials)continue;
  for(int s=0;s<130;s++){
   Gate h=c[j];
   if(s%4!=1)h.a=pick(nw);
   if(s%4!=0)h.b=pick(nw);
   if(h.a==h.b)continue;
   if(h.a>h.b)swap(h.a,h.b);
   if(s%7<3)h.isAnd=!h.isAnd;
   if(h.a==c[j].a&&h.b==c[j].b&&h.isAnd==c[j].isAnd)continue;
   Word value=ev(h,w);if(value==w[nw]&&s%8!=0)continue;
   Word diff=(lo|(value&care))^P.target;st.proposals++;
   int score=16*weighted(diff,hot,hotter);
   // Random nonnegative perturbation preserves exact solutions at temperature 0.
   if(temp)score+=pick(temp);
   if(score<best){best=score;chosen=j;choice=h;ties=1;}
   else if(score==best&&pick(++ties)==0){chosen=j;choice=h;}
   if(!diff){c[j]=h;return true;}
  }
 }
 if(chosen<0)return false;
 c[chosen]=choice;st.steps++;
 return false;
}
void dump(const Circuit& c){
 cout<<"{\"gates\":[";
 for(int j=0;j<(int)c.size();j++){if(j)cout<<',';cout<<"[\""<<(c[j].isAnd?"and":"or")<<"\","<<c[j].a<<','<<c[j].b<<']';}
 cout<<"]}\n";
}
int main(int argc,char**argv){
 int seconds=argc>1?atoi(argv[1]):60,sd=argc>2?atoi(argv[2]):20261125;rng.seed(sd);P.read();
 Circuit ctrl=seed(-1);
 if(ctrl.size()!=34||eval(ctrl)[P.n+ctrl.size()-1]!=P.target)throw runtime_error("canonical control failed");
 for(int i=0;i<P.np;i++){auto c=seed(i);scrambleOrder(c);if(c.size()!=33||((eval(c)[P.n+c.size()-1]^P.target)!=(Word(1)<<i)))throw runtime_error("omission control failed");}
 cout<<"canonical34 PASS full boundary "<<P.nt<<", all "<<P.np<<" distinct one-flag controls PASS, seed "<<sd<<'\n'<<flush;
 auto begin=chrono::steady_clock::now();Stats st;
 vector<Circuit> bank;
 for(int epoch=0;;epoch++){
  double elapsed=chrono::duration<double>(chrono::steady_clock::now()-begin).count();
  if(elapsed>=seconds){cout<<"{\"status\":\"NO_WITNESS_IN_BOUNDED_SEARCH\",\"steps\":"<<st.steps<<",\"evaluated_mutations\":"<<st.proposals<<",\"epochs\":"<<epoch<<",\"best_errors\":"<<st.best<<",\"distinct_one_error_masks\":"<<st.single.size()<<",\"seconds\":"<<elapsed<<"}\n";break;}
  Circuit c=bank.empty()||pick(3)==0?seed(pick(P.np)):bank[pick(bank.size())];scrambleOrder(c);
  Word hot=(Word(rng())<<96)|(Word(rng())<<64)|(Word(rng())<<32)|rng();
  Word hotter=(Word(rng())<<96)|(Word(rng())<<64)|(Word(rng())<<32)|rng();
  Circuit peak=c;int bestEpoch=weighted(eval(c)[P.n+c.size()-1]^P.target,hot,hotter);
  int length=20+pick(35);
  for(int j=0;j<length;j++){
   bool sat=step(c,hot,hotter,j<length/3?45:8,st);
   Word dif=eval(c)[P.n+c.size()-1]^P.target;
   if(sat||!dif){if(dif)throw runtime_error("SAT reevaluation failed");cout<<"SAT\n";dump(c);return 0;}
   int errors=pc(dif);st.best=min(st.best,errors);
   if(errors==1)st.single.insert({(uint64_t)dif,(uint64_t)(dif>>64)});
   int cost=weighted(dif,hot,hotter);
   if(cost<=bestEpoch){bestEpoch=cost;peak=c;}
  }
  if(bank.size()<100)bank.push_back(peak);else bank[pick(bank.size())]=peak;
 }
}
