#include <algorithm>
#include <array>
#include <chrono>
#include <csignal>
#include <iostream>
#include <random>
#include <vector>
using namespace std;
struct Clause {unsigned pos=0,neg=0;vector<int> lits;};
Clause clause(vector<int> a){Clause c;c.lits=a;for(int l:a){unsigned b=1u<<(abs(l)-1);if(l>0)c.pos|=b;else c.neg|=b;}return c;}
vector<Clause> base;
mt19937 rng;
volatile sig_atomic_t stopFlag=0;
void stopped(int){stopFlag=1;}
bool rup(const vector<Clause>&db,const Clause&c){
 if(c.pos&c.neg)return false;
 unsigned t=c.neg,f=c.pos;
 for(;;){bool change=false;for(const auto&d:db){if((d.pos&t)||(d.neg&f))continue;unsigned u=(d.pos|d.neg)&~(t|f);if(!u)return true;if(!(u&(u-1))){if(d.pos&u)t|=u;else f|=u;change=true;}}if(!change)return false;}
}
void minimize(vector<Clause>&run){
 bool changed=true;
 while(changed){changed=false;vector<int>order(run.size());for(int i=0;i<int(order.size());i++)order[i]=i;shuffle(order.begin(),order.end(),rng);
  for(int i:order){if(i>=int(run.size())||run[i].lits.empty())continue;auto trial=run;trial.erase(trial.begin()+i);auto db=base;bool valid=true;for(auto c:trial){if(!rup(db,c)){valid=false;break;}db.push_back(c);}if(valid){run=trial;changed=true;break;}}
 }
}
vector<Clause> solve(int mode){
 vector<Clause>db=base,learned;
 array<int,20>val{},level{},reason{},activity{};reason.fill(-1);vector<int>trail;int lev=0;unsigned t=0,f=0;
 auto assign=[&](int l,int why){int v=abs(l)-1;val[v]=l>0?1:-1;level[v]=lev;reason[v]=why;trail.push_back(l);if(l>0)t|=1u<<v;else f|=1u<<v;};
 auto backtrack=[&](int target){while(!trail.empty()&&level[abs(trail.back())-1]>target){int v=abs(trail.back())-1;trail.pop_back();val[v]=0;reason[v]=-1;t&=~(1u<<v);f&=~(1u<<v);}lev=target;};
 for(int steps=0;steps<5000;steps++){
  int conflict=-1;
  for(;;){bool changed=false;for(int q=0;q<int(db.size());q++){int i=(mode&8)?int(db.size())-1-q:q;auto&c=db[i];if((c.pos&t)||(c.neg&f))continue;unsigned u=(c.pos|c.neg)&~(t|f);if(!u){conflict=i;break;}if(!(u&(u-1))){int v=__builtin_ctz(u);assign(c.pos&u?v+1:-v-1,i);changed=true;}}if(conflict>=0||!changed)break;}
  if(conflict>=0){
   if(lev==0){auto c=clause({});if(!rup(db,c)){cerr<<"FAULT root conflict"<<endl;exit(2);}learned.push_back(c);minimize(learned);return learned;}
   vector<int>a;
   if((mode&3)==3){for(int l:trail)if(reason[abs(l)-1]<0)a.push_back(-l);}
   else{
    a.push_back(0);array<bool,20>seen{};int path=0,p=0,idx=int(trail.size())-1,ci=conflict;
    for(;;){for(int q:db[ci].lits){if(q==p)continue;int v=abs(q)-1;if(!seen[v]&&level[v]>0){seen[v]=true;if(level[v]==lev)path++;else a.push_back(q);}}
     while(idx>=0&&!seen[abs(trail[idx])-1])idx--;if(idx<0){cerr<<"FAULT analysis"<<endl;exit(2);}p=trail[idx--];int v=abs(p)-1;seen[v]=false;path--;
     bool more=path>0||((mode&3)==1&&reason[v]>=0)||((mode&3)==2&&reason[v]>=0&&rng()%2);
     if(!more){a[0]=-p;break;}ci=reason[v];if(ci<0){cerr<<"FAULT decision resolution"<<endl;exit(2);}
    }
   }
   sort(a.begin(),a.end());a.erase(unique(a.begin(),a.end()),a.end());Clause c=clause(a);if(!rup(db,c)){cerr<<"FAULT learned not RUP"<<endl;exit(2);}
   shuffle(a.begin(),a.end(),rng);for(int i=0;i<int(a.size());){auto b=a;b.erase(b.begin()+i);auto candidate=clause(b);if(rup(db,candidate)){a=b;c=candidate;}else i++;}
   if(c.lits.empty()){learned.push_back(c);minimize(learned);return learned;}
   for(int l:c.lits)activity[abs(l)-1]++;
   int high=-1,second=-1;for(int l:c.lits){int k=level[abs(l)-1];if(k>high){second=high;high=k;}else second=max(second,k);}
   int target=high>second?max(0,second):max(0,high-1);if((mode&4)||rng()%10==0)target=0;backtrack(target);db.push_back(c);learned.push_back(c);
   if(learned.size()>100)return {};
  }else{
   unsigned u=((1u<<20)-1)&~(t|f);if(!u){cerr<<"FAULT PHP satisfiable"<<endl;exit(2);}int chosen=-1,best=-1;
   for(int v=0;v<20;v++)if(u>>v&1){int s=rng()%32+((mode&16)?4*activity[v]:0);if(s>best){best=s;chosen=v;}}
   lev++;bool positive=rng()%100<((mode&32)?90:50);assign(positive?chosen+1:-chosen-1,-1);
  }
 }
 return {};
}
void show(const vector<Clause>&run,int trial){cout<<"BEST {\"trial\":"<<trial<<",\"length\":"<<run.size()<<",\"order\":\"oldest first\",\"run\":[";for(size_t i=0;i<run.size();i++){if(i)cout<<",";cout<<"[";for(size_t j=0;j<run[i].lits.size();j++){if(j)cout<<",";cout<<run[i].lits[j];}cout<<"]";}cout<<"]}"<<endl;}
int main(int argc,char**argv){
 for(int p=0;p<5;p++){vector<int>a;for(int h=0;h<4;h++)a.push_back(4*p+h+1);base.push_back(clause(a));}
 for(int p=0;p<5;p++)for(int q=p+1;q<5;q++)for(int h=0;h<4;h++)base.push_back(clause({-(4*p+h+1),-(4*q+h+1)}));
 rng.seed(argc>1?stoul(argv[1]):924801);int seconds=argc>2?stoi(argv[2]):600;signal(SIGINT,stopped);signal(SIGTERM,stopped);auto start=chrono::steady_clock::now();int best=100000;
 for(int trial=0;;trial++){
  if(stopFlag||chrono::duration<double>(chrono::steady_clock::now()-start).count()>seconds){cout<<"DONE trials="<<trial<<" best="<<best<<endl;return 0;}
  auto run=solve(rng()%64);if(run.empty())continue;if(int(run.size())<best){best=run.size();show(run,trial);if(best<=12)return 0;}
 }
}
