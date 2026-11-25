#include <array>
#include <vector>
#include <fstream>
#include <iostream>
#include <bit>
#include <cstdint>
#include <chrono>
using namespace std;
struct Gate{int op,a,b;bool na=false,nb=false;};
using TT=array<uint64_t,16>;
array<TT,10> inputs;TT target;
array<uint64_t,10> smallinputs;uint64_t smalltarget;
uint64_t evaluations=0,passed=0;
int full(const array<Gate,18>&c,int out,bool no) {
 array<TT,29>w{};for(int i=0;i<10;i++)w[i]=inputs[i];
 for(int i=0;i<18;i++)for(int k=0;k<16;k++){
  auto g=c[i];auto a=w[g.a][k],b=w[g.b][k];if(g.na)a=~a;if(g.nb)b=~b;
  w[10+i][k]=g.op?(a|b):(a&b);
 }
 int e=0;for(int k=0;k<16;k++)e+=popcount((no?~w[out][k]:w[out][k])^target[k]);return e;
}
bool check(const array<Gate,18>&c,int out,bool no) {
 array<uint64_t,29>w{};for(int i=0;i<10;i++)w[i]=smallinputs[i];
 for(int i=0;i<18;i++){
  auto g=c[i];auto a=w[g.a],b=w[g.b];if(g.na)a=~a;if(g.nb)b=~b;
  w[10+i]=g.op?(a|b):(a&b);
 }
 evaluations++;
 if(uint32_t((no?~w[out]:w[out])^smalltarget))return false;
 passed++;int e=full(c,out,no);if(e)return false;
 return true;
}
void print(const array<Gate,18>&c,int out,bool no,int mark,int seed,int d1,int d2,int r1,int r2){
 cout<<"FOUND seed="<<seed<<" drop="<<d1<<","<<d2<<" replace="<<r1<<","<<r2<<" mark="<<mark<<"\n";
 for(int j=0;j<18;j++)cout<<j+10<<" "<<c[j].op<<" "<<c[j].a<<" "<<c[j].na<<" "<<c[j].b<<" "<<c[j].nb<<"\n";
 cout<<"output "<<out<<" "<<no<<"\n";
}
int main(int argc,char**argv){
 if(argc!=3)return 2;int seconds=stoi(argv[2]);
 ifstream in(argv[1]);int count;in>>count;vector<array<Gate,20>>seeds(count);for(auto&seed:seeds)for(auto&g:seed)in>>g.op>>g.a>>g.b;
 vector<pair<int,int>>E={{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}};
 auto truth=[&](int r){for(auto[a,b]:E)if((r>>a&1)&&(r>>b&1))return true;return false;};
 vector<int> rows={0,1023};for(int r=0;r<1024;r++){
  for(int i=0;i<10;i++)if(r>>i&1)inputs[i][r/64]|=1ull<<(r%64);
  bool t=truth(r);if(t)target[r/64]|=1ull<<(r%64);
  bool critical=t&&popcount((unsigned)r)==2;
  if(!t){critical=true;for(int i=0;i<10;i++)if(!(r>>i&1)&&!truth(r|(1<<i)))critical=false;}
  if(critical)rows.push_back(r);
 }
 if(rows.size()!=32){cerr<<"bad rowcount "<<rows.size()<<"\n";return 3;}
 for(int k=0;k<32;k++){int r=rows[k];for(int i=0;i<10;i++)if(r>>i&1)smallinputs[i]|=1ull<<k;if(truth(r))smalltarget|=1ull<<k;}
 auto start=chrono::steady_clock::now();
 for(int sn=0;sn<count;sn++){
  auto seed=seeds[sn];
  for(int d1=0;d1<19;d1++)for(int d2=d1+1;d2<20;d2++)for(int q1=0;q1<=10+d1;q1++)for(int q2=0;q2<=10+d2;q2++){
   int r1=q1==10+d1?50:q1,r2=q2==10+d2?50:q2;
   auto map=[&](int v){if(v==10+d2)v=r2;if(v==10+d1)v=r1;if(v==50)return 28;return v-(v>10+d1)-(v>10+d2);};
   array<Gate,18> c;for(int j=0,k=0;j<20;j++)if(j!=d1&&j!=d2)c[k++]={seed[j].op,map(seed[j].a),map(seed[j].b)};
   int out=map(29);
   if(check(c,out,false)){print(c,out,false,0,sn,d1,d2,r1,r2);return 0;}
   for(int mark=0;mark<=28;mark++){
    array<int,37>places;int np=0;for(int j=0;j<18;j++){if(c[j].a==mark)places[np++]=2*j;if(c[j].b==mark)places[np++]=2*j+1;}if(out==mark)places[np++]=36;
    if(np>20)return 4;
    for(unsigned mask=1;mask<(1u<<np);mask++){
     bool no=false;for(int j=0;j<np;j++){int p=places[j];bool neg=(mask>>j)&1;if(p==36)no=neg;else if(p%2)c[p/2].nb=neg;else c[p/2].na=neg;}
     if(check(c,out,no)){print(c,out,no,mark,sn,d1,d2,r1,r2);return 0;}
    }
    for(int j=0;j<np;j++){int p=places[j];if(p<36){if(p%2)c[p/2].nb=false;else c[p/2].na=false;}}
   }
  }
  double elapsed=chrono::duration<double>(chrono::steady_clock::now()-start).count();
  cout<<"completed seed="<<sn<<" evaluations="<<evaluations<<" criticalpasses="<<passed<<" elapsed="<<elapsed<<"\n";cout.flush();
  if(elapsed>seconds)break;
 }
 cout<<"DONE no witness evaluations="<<evaluations<<" criticalpasses="<<passed<<"\n";
}
