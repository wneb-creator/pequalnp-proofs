#include <array>
#include <vector>
#include <iostream>
#include <unordered_set>
#include <cstdint>
using namespace std;
struct Gate {int op,a,b;uint32_t value;};
vector<uint32_t> values;
vector<Gate> path;
uint32_t target;
uint64_t nodes=0, trials=0;
bool dfs(int depth,int limit,bool hasnot) {
 nodes++;
 unordered_set<uint64_t> seen;
 int n=values.size();
 for(int op=0;op<3;op++)for(int a=0;a<n;a++)for(int b=(op==2?a:0);b<(op==2?a+1:n);b++) {
  if(op<2 && a>=b)continue;
  trials++;
  uint32_t v=op==0?(values[a]&values[b]):op==1?(values[a]|values[b]):~values[a];
  bool hn=hasnot||op==2;
  if(v==target) {
   path.push_back({op,a,b,v});
   cout<<"FOUND gates="<<path.size()<<" hasnot="<<hn<<"\n";
   for(int i=0;i<(int)path.size();i++)cout<<8+i<<" "<<path[i].op<<" "<<path[i].a<<" "<<path[i].b<<"\n";
   return true;
  }
  if(depth+1>=limit)continue;
  bool old=false;for(auto w:values)if(v==w)old=true;
  if(old)continue;
  if(!seen.insert((uint64_t(v)<<1)|hn).second)continue;
  values.push_back(v);path.push_back({op,a,b,v});
  if(dfs(depth+1,limit,hn))return true;
  path.pop_back();values.pop_back();
 }
 return false;
}
int main(int argc,char**argv) {
 int lim=argc>1?stoi(argv[1]):4;
 values.resize(8);
 for(int r=0;r<32;r++)for(int i=0;i<5;i++)if(r>>i&1)values[i]|=1u<<r;
 values[5]=values[1]|values[4];values[6]=values[3]|values[4];values[7]=0;
 target=(values[1]&values[0])|(values[1]&values[3])|(values[2]&values[0])|(values[2]&values[4]);
 bool found=dfs(0,lim,false);
 cout<<"completed found="<<found<<" limit="<<lim<<" nodes="<<nodes<<" gate_trials="<<trials<<"\n";
}
