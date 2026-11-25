#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <ctime>
#include <map>
#include <vector>
#include <algorithm>
#include <string>
#include <sys/resource.h>
constexpr uint32_t MOD=1000000007U;
static void readx(FILE*f,void*p,size_t n){if(fread(p,n,1,f)!=1)exit(2);}
static uint32_t inverse(uint32_t x){uint64_t a=x,b=1;uint32_t e=MOD-2;while(e){if(e&1)b=b*a%MOD;a=a*a%MOD;e>>=1;}return b;}
using Row=std::vector<std::pair<uint32_t,uint32_t>>;
int main(int argc,char**argv){
 if(argc!=4){fprintf(stderr,"Usage: graded-sparse matrix.bin degrees.bin output.jsonl\n");return 2;}
 FILE*f=std::string(argv[1])=="-"?stdin:fopen(argv[1],"rb");FILE*d=fopen(argv[2],"rb");if(!f||!d)return 2;
 uint32_t nr,nc;uint64_t nnz;readx(f,&nr,4);readx(f,&nc,4);readx(f,&nnz,8);
 std::vector<uint32_t> degree(nc),order(nc),mapping(nc);readx(d,degree.data(),nc*4);fclose(d);
 uint32_t at=0;for(int n=12;n>=0;n--)for(uint32_t i=0;i<nc;i++)if(degree[i]==(uint32_t)n)order[at++]=i;
 if(at!=nc)return 2;for(uint32_t i=0;i<nc;i++)mapping[order[i]]=i;
 std::vector<Row> pivots(nc);std::map<uint32_t,uint32_t> row;uint32_t rank=0,counts[13]={0};uint64_t final_nnz=0,reductions=0;clock_t start=clock();
 auto insert_row=[&](){
  while(!row.empty()){
   auto first=row.begin();uint32_t col=first->first,factor=first->second;
   if(pivots[col].empty()){
    uint32_t inv=inverse(factor);Row&target=pivots[col];target.reserve(row.size());
    for(auto entry:row)target.emplace_back(entry.first,(uint64_t)entry.second*inv%MOD);
    counts[degree[order[col]]]++;rank++;final_nnz+=target.size();row.clear();return;
   }
   reductions++;
   for(auto entry:pivots[col]){
    uint32_t product=(uint64_t)factor*entry.second%MOD;auto it=row.find(entry.first);
    uint32_t current=it==row.end()?0:it->second;
    uint32_t value=current+MOD-product;if(value>=MOD)value-=MOD;
    if(!value){if(it!=row.end())row.erase(it);}
    else if(it==row.end())row.emplace(entry.first,value);else it->second=value;
   }
  }
 };
 uint32_t previous=0;
 for(uint64_t k=0;k<nnz;k++){
  uint32_t r,c;int64_t v;readx(f,&r,4);readx(f,&c,4);readx(f,&v,8);if(r>=nr||c>=nc||r<previous)return 2;
  if(r!=previous){insert_row();previous=r;if(r%500==0){fprintf(stderr,"input_row=%u rank=%u stored_nnz=%llu cpu=%.3f\n",r,rank,(unsigned long long)final_nnz,(double)(clock()-start)/CLOCKS_PER_SEC);fflush(stderr);}}
  v%=MOD;if(v<0)v+=MOD;if(v)row[mapping[c]]=(uint32_t)v;
 }
 insert_row();if(fgetc(f)!=EOF)return 2;fclose(f);
 FILE*out=fopen(argv[3],"w");if(!out)return 2;
 for(uint32_t col=0;col<nc;col++)if(!pivots[col].empty()&&degree[order[col]]==0){fprintf(out,"{\"degree\":%u,\"terms\":[",degree[order[col]]);bool first=true;for(auto entry:pivots[col]){fprintf(out,"%s[%u,%u]",first?"":",",order[entry.first],entry.second);first=false;}fprintf(out,"]}\n");}
 fclose(out);rusage usage;getrusage(RUSAGE_SELF,&usage);printf("RANK %u CPU %.6f RSS_KIB %ld STORED_NNZ %llu REDUCTIONS %llu\n",rank,(double)(clock()-start)/CLOCKS_PER_SEC,usage.ru_maxrss,(unsigned long long)final_nnz,(unsigned long long)reductions);
 for(uint32_t n=0;n<=12;n++)if(counts[n])printf("PIVOT degree=%u count=%u\n",n,counts[n]);return 0;
}
