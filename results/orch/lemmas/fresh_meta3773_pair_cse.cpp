// Enumerate formulas and DAGs that become formulas after making one internal wire free.
// Input is list of distinct free feature truth tables, target and its number of row bits.
#include <algorithm>
#include <chrono>
#include <iostream>
#include <string>
#include <vector>
using namespace std;
struct Item { int cost=-1; int a=0, b=0, op=-1; };
struct DP { vector<Item> by; vector<vector<int>> layers; };
DP solve(const vector<int>& leaves,int size,int cost_limit,int target){
 DP dp{vector<Item>(size),vector<vector<int>>(cost_limit+1)};
 for(int leaf:leaves) if(dp.by[leaf].cost<0){dp.by[leaf].cost=0;dp.layers[0].push_back(leaf);}
 for(int d=1;d<=cost_limit && (target<0 || dp.by[target].cost<0);d++) {
  for(int i=0;2*i<=d-1;i++) for(int a:dp.layers[i]) for(int b:dp.layers[d-1-i]) {
   const int vals[2]={a|b,a&b};
   for(int k=0;k<2;k++)if(dp.by[vals[k]].cost<0){dp.by[vals[k]]={d,a,b,k};dp.layers[d].push_back(vals[k]);}
  }
 }
 return dp;
}
string show(const DP& dp,int t){ const Item& it=dp.by[t];if(it.cost==0)return to_string(t);return "("+show(dp,it.a)+(it.op==0?"|":"&")+show(dp,it.b)+")";}
int main(){int size,limit,target,count;cin>>size>>limit>>target>>count;vector<int> leaves(count);for(int&x:leaves)cin>>x;
 DP base=solve(leaves,size,limit-1,-1); long long tested=0;
 for(int c=1;c<limit;c++)for(int inter:base.layers[c]){
  leaves.push_back(inter);DP extra=solve(leaves,size,limit-c,target);leaves.pop_back();tested++;
  if(extra.by[target].cost>=0){cout<<"HIT cost "<<c+extra.by[target].cost<<" intermediate "<<inter<<"="<<show(base,inter)<<" output "<<show(extra,target)<<"\n";}
 }
 cout<<"checked one-shared-gate factorizations for "<<tested<<" distinct intermediate functions; bound "<<limit<<"\n";
}
