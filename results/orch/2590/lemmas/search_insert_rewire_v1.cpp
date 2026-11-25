#include <array>
#include <vector>
#include <iostream>
#include <cstdint>
#include <chrono>
using namespace std;
struct Gate{int op,a,b;};
const array<Gate,18> base={{{1,2,9},{1,10,5},{1,9,3},{1,0,6},{1,3,5},{1,6,14},{1,0,12},{1,13,2},{0,17,15},{0,4,16},{0,18,16},{1,7,20},{0,17,1},{1,19,22},{0,15,8},{0,21,11},{1,25,24},{1,23,26}}};
const array<uint64_t,10> input={1361186ULL,2208273ULL,4409482ULL,17437748ULL,135004873ULL,42997773ULL,337641582ULL,549454704ULL,117465984ULL,939555840ULL};
const uint64_t goal=1073709056ULL;
uint64_t tests=0;int best=1000;
void test(int pos,int op,int a,int b,const vector<int>&slots){
 array<uint64_t,28>w;for(int i=0;i<10;i++)w[i]=input[i];
 uint64_t newvalue=0;
 auto redirected=[&](int slot){for(int s:slots)if(s==slot)return true;return false;};
 for(int j=0;j<=18;j++){
  if(j==pos)newvalue=op?(w[a]|w[b]):(w[a]&w[b]);
  if(j==18)break;
  auto g=base[j];uint64_t x=redirected(2*j)?newvalue:w[g.a],y=redirected(2*j+1)?newvalue:w[g.b];
  w[10+j]=g.op?(x|y):(x&y);
 }
 uint64_t out=redirected(36)?newvalue:w[27];int fp=__builtin_popcountll(out&~goal),fn=__builtin_popcountll(goal&~out);tests++;
 if(fp+fn<best){
  best=fp+fn;cout<<"score fp="<<fp<<" fn="<<fn<<" tests="<<tests<<" pos="<<pos<<" op="<<op<<" a="<<a<<" b="<<b<<" redirects=";
  for(int s:slots)cout<<s<<",";cout<<"\n";cout.flush();
 }
 if(fp==0&&fn==0){
  cout<<"FOUND\n";
  auto mapped=[&](int x){return x+(x>=10+pos);};
  for(int j=0;j<=18;j++){
   if(j==pos)cout<<10+pos<<" "<<op<<" "<<a<<" "<<b<<"\n";
   if(j<18){auto g=base[j];cout<<10+j+(j>=pos)<<" "<<g.op<<" "<<(redirected(2*j)?10+pos:mapped(g.a))<<" "<<(redirected(2*j+1)?10+pos:mapped(g.b))<<"\n";}
  }
  cout<<"OUTPUT "<<(redirected(36)?10+pos:mapped(27))<<"\n";exit(0);
 }
}
int main(){
 auto start=chrono::steady_clock::now();
 for(int pos=0;pos<=18;pos++){
  for(int x=2*pos;x<=36;x++){
   vector<int>s{x};
   auto run=[&](){for(int a=0;a<10+pos;a++)for(int b=a;b<10+pos;b++)for(int op=0;op<2;op++)test(pos,op,a,b,s);};
   run();
   for(int y=x+1;y<=36;y++){
    s.push_back(y);run();
    for(int z=y+1;z<=36;z++){s.push_back(z);run();s.pop_back();}
    s.pop_back();
   }
  }
 }
 cout<<"DONE tests="<<tests<<" best_critical_errors="<<best<<" elapsed="<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<"\n";
}
