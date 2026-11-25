#include <vector>
#include <array>
#include <iostream>
#include <cstdint>
using namespace std;
struct Gate{int op,a,b;};
array<uint64_t,20>w;
array<Gate,3>gs;
uint64_t mask,target;
long long count=0;
bool found=false;
void rec(int n,int nots){
 int width=14+n;
 if(n&&((w[width-1]&mask)==target)&&(n<3||nots)){
  cout<<"WITNESS gates "<<n<<" nots "<<nots<<" (pad with dead NOT if needed)\n";
  for(int j=0;j<n;j++)cout<<gs[j].op<<' '<<gs[j].a<<' '<<gs[j].b<<'\n';found=true;return;
 }
 if(n==3){count++;return;}
 for(int op=0;op<3&&!found;op++)for(int a=0;a<width&&!found;a++)for(int b=(op==2?a:a+1);b<(op==2?a+1:width)&&!found;b++){
  if(n==2&&nots==0&&op!=2)continue;
  w[width]=op==0?w[a]&w[b]:op==1?w[a]|w[b]:~w[a];gs[n]={op,a,b};rec(n+1,nots+(op==2));
 }
}
int main(){
 vector<int>raw={0,2,4,6,7,8};
 vector<vector<int>>S={{0},{2},{4},{6},{7},{8},{6,7},{0,2},{0,7},{0,7,8},{0,2,6},{4,8},{2,4,8},{4,6,7}};
 for(int x=0;x<64;x++){
  bool b[10]={};for(int i=0;i<6;i++)b[raw[i]]=x>>i&1;
  for(int j=0;j<14;j++)for(int i:S[j])if(b[i]){w[j]|=1ull<<x;break;}
  if(b[2]||b[4]||b[8])mask|=1ull<<x;
  if((b[0]&&b[4])||(b[2]&&b[7])||(b[6]&&b[8]))target|=1ull<<x;
 }
 rec(0,0);cout<<"finished found="<<found<<" checked="<<count<<'\n';
}
