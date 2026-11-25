#include <algorithm>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>
#include <chrono>
using u64=uint64_t; using u32=uint32_t;
struct Pair{int index;u32 value;};
struct Pivot{int origin;u32 inv;std::vector<Pair> data, deps;};
struct Field{u64 p,recip; explicit Field(u64 prime):p(prime),recip(UINT64_MAX/prime){}
 u32 mul(u64 a,u64 b)const{u64 x=a*b;u64 q=(u64)(((__uint128_t)x*recip)>>64);u64 r=x-q*p;while(r>=p)r-=p;return(u32)r;}
 u32 sub(u32 a,u32 b)const{return a>=b?a-b:(u32)(a+p-b);}
 u32 pow(u32 a,u64 n)const{u32 r=1;while(n){if(n&1)r=mul(r,a);a=mul(a,a);n>>=1;}return r;}
};
int main(int argc,char**argv){if(argc!=4)return 2;std::ifstream in(argv[1]);std::ofstream out(argv[2]);u64 prime=std::stoull(argv[3]);if(prime<3||prime>2147483647)return 3;Field f(prime);int cols,rows;in>>cols>>rows;std::vector<int> bycol(cols,-1);std::vector<Pivot> pivots;std::vector<u32> work(cols);int target=-1;auto start=std::chrono::steady_clock::now();
for(int row=0;row<rows;row++){std::fill(work.begin(),work.end(),0);int count;in>>count;for(int k=0;k<count;k++){int col;int64_t coeff;in>>col>>coeff;coeff%=(int64_t)prime;if(coeff<0)coeff+=prime;work[col]=(u32)coeff;}Pivot pivot;pivot.origin=row;pivot.inv=1;
for(int col=0;col<cols;col++){u32 coefficient=work[col];if(!coefficient)continue;int old=bycol[col];if(old>=0){pivot.deps.push_back({old,coefficient});for(auto term:pivots[old].data)work[term.index]=f.sub(work[term.index],f.mul(coefficient,term.value));}else{pivot.inv=f.pow(coefficient,prime-2);for(int j=col;j<cols;j++)if(work[j])pivot.data.push_back({j,f.mul(work[j],pivot.inv)});bycol[col]=(int)pivots.size();pivots.push_back(std::move(pivot));if(col==cols-1)target=(int)pivots.size()-1;break;}}
if(row%200==0)std::cout<<"row "<<row<<" rank "<<pivots.size()<<std::endl;if(target>=0)break;
}
double secs=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();std::cout<<"finished rank "<<pivots.size()<<" unit "<<(target>=0)<<" seconds "<<secs<<std::endl;
u64 fingerprint=1469598103934665603ULL;for(auto &pivot:pivots){fingerprint^=(u64)pivot.origin;fingerprint*=1099511628211ULL;fingerprint^=(u64)pivot.data[0].index;fingerprint*=1099511628211ULL;}
out<<"{\"fingerprint\":\""<<fingerprint<<"\",\"prime\":"<<prime<<",\"rank\":"<<pivots.size()<<",\"unit\":"<<(target>=0?"true":"false")<<",\"seconds\":"<<secs;
if(target>=0){std::vector<u32> weights(pivots.size()),witness(rows);weights[target]=1;for(int k=target;k>=0;k--){u32 w=f.mul(weights[k],pivots[k].inv);witness[pivots[k].origin]=w;for(auto dep:pivots[k].deps)weights[dep.index]=f.sub(weights[dep.index],f.mul(w,dep.value));}out<<",\"witness\":[";for(int j=0;j<rows;j++){if(j)out<<",";out<<witness[j];}out<<"]";}
out<<"}\n";return 0;}
