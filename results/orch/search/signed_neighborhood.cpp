#include <array>
#include <vector>
#include <fstream>
#include <iostream>
#include <bit>
#include <cstdint>
using namespace std;
struct Gate{int op,a,b;bool na=false,nb=false;};
using TT=array<uint64_t,16>;
array<TT,10> inputs;
TT target;
long long evaluations=0;
int eval(const vector<Gate>&c,int out,bool no) {
 array<TT,29>w{};for(int i=0;i<10;i++)w[i]=inputs[i];
 for(int i=0;i<(int)c.size();i++) {
  auto g=c[i];
  for(int k=0;k<16;k++){
   auto a=w[g.a][k],b=w[g.b][k];if(g.na)a=~a;if(g.nb)b=~b;
   w[10+i][k]=g.op?(a|b):(a&b);
  }
 }
 int e=0;for(int k=0;k<16;k++)e+=popcount((no?~w[out][k]:w[out][k])^target[k]);
 evaluations++;return e;
}
int main(int argc,char**argv) {
 if(argc!=2)return 2;
 ifstream in(argv[1]);vector<Gate> seed(19);for(auto&g:seed)in>>g.op>>g.a>>g.b;
 vector<pair<int,int>> E={{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}};
 for(int r=0;r<1024;r++){
  for(int i=0;i<10;i++)if(r>>i&1)inputs[i][r/64]|=1ull<<(r%64);
  for(auto[a,b]:E)if((r>>a&1)&&(r>>b&1)){target[r/64]|=1ull<<(r%64);break;}
 }
 int best=1024;
 for(int drop=0;drop<19;drop++)for(int rr=0;rr<=10+drop;rr++){
  int replacement=rr==10+drop?28:rr;
  auto remap=[&](int v){if(v==10+drop)return replacement;return v>10+drop?v-1:v;};
  vector<Gate> c;for(int j=0;j<19;j++)if(j!=drop)c.push_back({seed[j].op,remap(seed[j].a),remap(seed[j].b)});
  int out=remap(28);
  for(int mark=0;mark<=28;mark++){
   vector<int> places;for(int j=0;j<18;j++){if(c[j].a==mark)places.push_back(2*j);if(c[j].b==mark)places.push_back(2*j+1);}if(out==mark)places.push_back(36);
   if(places.size()>20)return 3;
   for(unsigned mask=0;mask<(1u<<places.size());mask++){
    bool no=false;
    for(int j=0;j<(int)places.size();j++){
     int p=places[j];bool neg=(mask>>j)&1;
     if(p==36)no=neg;else if(p%2)c[p/2].nb=neg;else c[p/2].na=neg;
    }
    int e=eval(c,out,no);
    if(e<best){best=e;cout<<"best="<<e<<" drop="<<drop<<" replacement="<<replacement<<" marked="<<mark<<" evals="<<evaluations<<"\n";}
    if(!e){for(int j=0;j<18;j++)cout<<j+10<<" "<<c[j].op<<" "<<c[j].a<<" "<<c[j].na<<" "<<c[j].b<<" "<<c[j].nb<<"\n";cout<<"output "<<out<<" "<<no<<"\n";return 0;}
   }
   for(int p:places)if(p<36){if(p%2)c[p/2].nb=false;else c[p/2].na=false;}
  }
 }
 cout<<"COMPLETED no witness; best="<<best<<" evals="<<evaluations<<"\n";
}
