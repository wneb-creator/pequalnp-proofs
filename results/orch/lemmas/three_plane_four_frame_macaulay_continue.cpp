#include <algorithm>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>
#include <chrono>
#include <cstdio>
#include <climits>
#include <stdexcept>
using u64=uint64_t; using u32=uint32_t;
struct Pair{int index;u32 value;};
struct Pivot{int origin;u32 inv;std::vector<Pair> data, deps;};
struct Field{u64 p,recip; explicit Field(u64 prime):p(prime),recip(UINT64_MAX/prime){}
 u32 mul(u64 a,u64 b)const{u64 x=a*b;u64 q=(u64)(((__uint128_t)x*recip)>>64);u64 r=x-q*p;while(r>=p)r-=p;return(u32)r;}
 u32 sub(u32 a,u32 b)const{return a>=b?a-b:(u32)(a+p-b);}
 u32 pow(u32 a,u64 n)const{u32 r=1;while(n){if(n&1)r=mul(r,a);a=mul(a,a);n>>=1;}return r;}
};

template<class T> void put(std::ostream& o,const T& v){o.write(reinterpret_cast<const char*>(&v),sizeof(T));if(!o)throw std::runtime_error("checkpoint write failed");}
template<class T> void get(std::istream& i,T& v){i.read(reinterpret_cast<char*>(&v),sizeof(T));if(!i)throw std::runtime_error("checkpoint read failed");}
u64 filehash(const char* path){std::ifstream f(path,std::ios::binary);if(!f)throw std::runtime_error("matrix open failed");u64 h=1469598103934665603ULL;char b[65536];while(f){f.read(b,sizeof(b));for(std::streamsize k=0;k<f.gcount();k++){h^=(unsigned char)b[k];h*=1099511628211ULL;}}return h;}
void save(const std::string& path,u64 hash,const std::string& binding,u64 prime,int cols,int rows,int next,std::streamoff offset,const std::vector<Pivot>& pivots){
 std::string tmp=path+".tmp";std::ofstream o(tmp,std::ios::binary);u64 magic=0x504e504d414332ULL;put(o,magic);for(char c:binding)put(o,c);put(o,hash);put(o,prime);put(o,cols);put(o,rows);put(o,next);put(o,offset);u64 size=pivots.size();put(o,size);
 for(const auto& p:pivots){put(o,p.origin);put(o,p.inv);u64 nd=p.data.size(),ne=p.deps.size();put(o,nd);put(o,ne);for(auto t:p.data){put(o,t.index);put(o,t.value);}for(auto t:p.deps){put(o,t.index);put(o,t.value);}}
 o.close();if(!o||std::rename(tmp.c_str(),path.c_str()))throw std::runtime_error("checkpoint replace failed");
}
int restore(const std::string& path,u64 hash,const std::string& binding,u64 prime,int cols,int rows,std::ifstream& matrix,std::vector<Pivot>& pivots,std::vector<int>& bycol){
 std::ifstream in(path,std::ios::binary);if(!in)return 0;u64 magic,h,p,size;int c,r,next;std::streamoff offset;get(in,magic);std::string stored(128,'0');for(char& ch:stored)get(in,ch);get(in,h);get(in,p);get(in,c);get(in,r);get(in,next);get(in,offset);get(in,size);
 if(magic!=0x504e504d414332ULL||stored!=binding||h!=hash||p!=prime||c!=cols||r!=rows||next<0||next>rows||size>(u64)cols||size>(u64)next)throw std::runtime_error("checkpoint header mismatch");
 for(u64 k=0;k<size;k++){Pivot pivot;u64 nd,ne;get(in,pivot.origin);get(in,pivot.inv);get(in,nd);get(in,ne);if(pivot.origin<0||pivot.origin>=next||!pivot.inv||pivot.inv>=prime||!nd||nd>(u64)cols||ne>k)throw std::runtime_error("invalid checkpoint pivot");
  for(u64 j=0;j<nd;j++){Pair t;get(in,t.index);get(in,t.value);if(t.index<0||t.index>=cols||!t.value||t.value>=prime||(j&&t.index<=pivot.data.back().index))throw std::runtime_error("invalid checkpoint row");pivot.data.push_back(t);}
  for(u64 j=0;j<ne;j++){Pair t;get(in,t.index);get(in,t.value);if(t.index<0||(u64)t.index>=k||!t.value||t.value>=prime)throw std::runtime_error("invalid checkpoint dependency");pivot.deps.push_back(t);}
  int col=pivot.data.front().index;if(pivot.data.front().value!=1||bycol[col]!=-1)throw std::runtime_error("invalid checkpoint leading term");bycol[col]=(int)k;pivots.push_back(std::move(pivot));
 }
 matrix.seekg(offset);if(!matrix)throw std::runtime_error("checkpoint matrix position failed");return next;
}

int main(int argc,char**argv){if(argc!=8&&argc!=9)return 2;std::string binding=std::string(argv[6])+argv[7];if(binding.size()!=128||binding.find_first_not_of("0123456789abcdef")!=std::string::npos)return 5;std::ifstream in(argv[1]);std::ofstream out(argv[2]);u64 prime=std::stoull(argv[3]);if(prime<3||prime>2147483647)return 3;Field f(prime);int cols,rows;in>>cols>>rows;std::vector<int> bycol(cols,-1);std::vector<Pivot> pivots;std::vector<u32> work(cols);int target=-1;auto start=std::chrono::steady_clock::now();u64 hash=filehash(argv[1]);int first=restore(argv[4],hash,binding,prime,cols,rows,in,pivots,bycol);target=bycol[cols-1];int completed=first;double budget=std::stod(argv[5]);int row_budget=argc==9?std::stoi(argv[8]):INT_MAX;if(budget<=0||row_budget<=0)return 4;std::cout<<"resume row "<<first<<" rank "<<pivots.size()<<std::endl;
for(int row=first;row<rows;row++){std::fill(work.begin(),work.end(),0);int count;in>>count;for(int k=0;k<count;k++){int col;int64_t coeff;in>>col>>coeff;coeff%=(int64_t)prime;if(coeff<0)coeff+=prime;work[col]=(u32)coeff;}Pivot pivot;pivot.origin=row;pivot.inv=1;
for(int col=0;col<cols;col++){u32 coefficient=work[col];if(!coefficient)continue;int old=bycol[col];if(old>=0){pivot.deps.push_back({old,coefficient});for(auto term:pivots[old].data)work[term.index]=f.sub(work[term.index],f.mul(coefficient,term.value));}else{pivot.inv=f.pow(coefficient,prime-2);for(int j=col;j<cols;j++)if(work[j])pivot.data.push_back({j,f.mul(work[j],pivot.inv)});bycol[col]=(int)pivots.size();pivots.push_back(std::move(pivot));if(col==cols-1)target=(int)pivots.size()-1;break;}}
if(row%200==0)std::cout<<"row "<<row<<" rank "<<pivots.size()<<std::endl;completed=row+1;
if(row+1<rows&&(row-first+1>=row_budget||std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()>=budget)){save(argv[4],hash,binding,prime,cols,rows,row+1,(std::streamoff)in.tellg(),pivots);out<<"{\"checkpointed\":true,\"next_row\":"<<row+1<<",\"rank\":"<<pivots.size()<<"}\n";return 0;}
}
std::streamoff final_offset=in.tellg();if(final_offset<0){in.clear();in.seekg(0,std::ios::end);final_offset=in.tellg();}save(argv[4],hash,binding,prime,cols,rows,completed,final_offset,pivots);
double secs=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();std::cout<<"finished rank "<<pivots.size()<<" unit "<<(target>=0)<<" seconds "<<secs<<std::endl;
u64 fingerprint=1469598103934665603ULL;for(auto &pivot:pivots){fingerprint^=(u64)pivot.origin;fingerprint*=1099511628211ULL;fingerprint^=(u64)pivot.data[0].index;fingerprint*=1099511628211ULL;}
out<<"{\"complete\":true,\"next_row\":"<<completed<<",\"fingerprint\":\""<<fingerprint<<"\",\"prime\":"<<prime<<",\"rank\":"<<pivots.size()<<",\"unit\":"<<(target>=0?"true":"false")<<",\"seconds\":"<<secs;
if(target>=0){std::vector<u32> weights(pivots.size()),witness(rows);weights[target]=1;for(int k=target;k>=0;k--){u32 w=f.mul(weights[k],pivots[k].inv);witness[pivots[k].origin]=w;for(auto dep:pivots[k].deps)weights[dep.index]=f.sub(weights[dep.index],f.mul(w,dep.value));}out<<",\"witness\":[";for(int j=0;j<rows;j++){if(j)out<<",";out<<witness[j];}out<<"]";}
out<<"}\n";return 0;}
