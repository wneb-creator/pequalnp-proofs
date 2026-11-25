#include <flint/fmpz.h>
#include <flint/fmpq.h>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <ctime>
#include <map>
#include <vector>
#include <string>
#include <sys/resource.h>
struct Q{
 fmpq_t v;
 Q(){fmpq_init(v);}Q(long x){fmpq_init(v);fmpq_set_si(v,x,1);}
 Q(const Q&x){fmpq_init(v);fmpq_set(v,x.v);}Q(Q&&x)noexcept{fmpq_init(v);fmpq_swap(v,x.v);}
 Q&operator=(const Q&x){fmpq_set(v,x.v);return*this;}Q&operator=(Q&&x)noexcept{fmpq_swap(v,x.v);return*this;}
 ~Q(){fmpq_clear(v);}bool zero()const{return fmpq_is_zero(v);}
};
static Q mul(const Q&a,const Q&b){Q c;fmpq_mul(c.v,a.v,b.v);return c;}
static Q inverse(const Q&a){Q c;fmpq_inv(c.v,a.v);return c;}
static void addto(Q&a,const Q&b){fmpq_add(a.v,a.v,b.v);}
static void subfrom(Q&a,const Q&b){fmpq_sub(a.v,a.v,b.v);}
static void printq(FILE*f,const Q&q){char*s=fmpq_get_str(NULL,10,q.v);fprintf(f,"\"%s\"",s);flint_free(s);}
static void readx(FILE*f,void*p,size_t n){if(fread(p,n,1,f)!=1)exit(2);}
using Row=std::vector<std::pair<uint32_t,Q>>;
struct Node{uint32_t input;Q scale;std::vector<std::pair<uint32_t,Q>> dependencies;};
int main(int argc,char**argv){
 if(argc!=4){fprintf(stderr,"Usage: graded-rational matrix.bin degrees.bin output.jsonl\n");return 2;}
 FILE*f=fopen(argv[1],"rb"),*d=fopen(argv[2],"rb");if(!f||!d)return 2;uint32_t nr,nc;uint64_t nnz;readx(f,&nr,4);readx(f,&nc,4);readx(f,&nnz,8);
 std::vector<uint32_t> degree(nc),rowdegree(nr),order(nc),mapping(nc);readx(d,degree.data(),nc*4);readx(d,rowdegree.data(),nr*4);fclose(d);
 uint32_t at=0;for(int n=12;n>=0;n--)for(uint32_t i=0;i<nc;i++)if(degree[i]==(uint32_t)n)order[at++]=i;
 if(at!=nc)return 2;for(uint32_t i=0;i<nc;i++)mapping[order[i]]=i;
 std::vector<Row> pivots(nc);std::vector<uint32_t> pivotnode(nc),targets,targetcols;std::vector<Node> nodes;std::map<uint32_t,Q> row;uint32_t rank=0,counts[13]={0};uint64_t final_nnz=0,reductions=0;clock_t start=clock();
 auto insert_row=[&](uint32_t input){
  std::vector<std::pair<uint32_t,Q>> dependencies;
  while(!row.empty()){
   auto first=row.begin();uint32_t col=first->first;Q factor=first->second;
   if(pivots[col].empty()){
    Q inv=inverse(factor);Row&target=pivots[col];target.reserve(row.size());
    for(const auto&entry:row)target.emplace_back(entry.first,mul(entry.second,inv));
    pivotnode[col]=nodes.size();nodes.push_back(Node{input,std::move(inv),std::move(dependencies)});
    if(rowdegree[input]>4&&degree[order[col]]<=4){targets.push_back(nodes.size()-1);targetcols.push_back(col);fprintf(stderr,"NEW_LOW_DEGREE input=%u target=%zu degree=%u terms=%zu\n",input,targets.size(),degree[order[col]],target.size());fflush(stderr);}
    counts[degree[order[col]]]++;rank++;final_nnz+=target.size();row.clear();return;
   }
   reductions++;dependencies.emplace_back(pivotnode[col],factor);
   for(const auto&entry:pivots[col]){
    Q product=mul(factor,entry.second);auto it=row.find(entry.first);
    if(it==row.end()){fmpq_neg(product.v,product.v);row.emplace(entry.first,std::move(product));}
    else{subfrom(it->second,product);if(it->second.zero())row.erase(it);}
   }
  }
 };
 uint32_t previous=0;
 for(uint64_t k=0;k<nnz;k++){
  uint32_t r,c;int64_t v;readx(f,&r,4);readx(f,&c,4);readx(f,&v,8);if(r>=nr||c>=nc||r<previous)return 2;
  if(r!=previous){insert_row(previous);previous=r;if(r%500==0){fprintf(stderr,"input_row=%u rank=%u stored_nnz=%llu cpu=%.3f\n",r,rank,(unsigned long long)final_nnz,(double)(clock()-start)/CLOCKS_PER_SEC);fflush(stderr);}}
  if(v)row.emplace(mapping[c],Q(v));
 }
 insert_row(previous);fclose(f);FILE*out=fopen(argv[3],"w");if(!out)return 2;
 for(size_t t=0;t<targets.size();t++){
  uint32_t target=targets[t],col=targetcols[t];std::vector<Q> weights(target+1);weights[target]=Q(1);std::map<uint32_t,Q> certificate;
  for(int64_t i=target;i>=0;i--){if(weights[i].zero())continue;const Node&node=nodes[i];Q scale=mul(weights[i],node.scale);addto(certificate[node.input],scale);for(const auto&dep:node.dependencies)subfrom(weights[dep.first],mul(scale,dep.second));}
  fprintf(out,"{\"target\":%zu,\"degree\":%u,\"polynomial\":[",t,degree[order[col]]);bool first=true;
  for(const auto&entry:pivots[col]){fprintf(out,"%s[%u,",first?"":",",order[entry.first]);printq(out,entry.second);fprintf(out,"]");first=false;}
  fprintf(out,"],\"certificate\":[");first=true;
  for(const auto&entry:certificate)if(!entry.second.zero()){fprintf(out,"%s[%u,",first?"":",",entry.first);printq(out,entry.second);fprintf(out,"]");first=false;}
  fprintf(out,"]}\n");fflush(out);
 }
 fclose(out);rusage usage;getrusage(RUSAGE_SELF,&usage);printf("RANK %u TARGETS %zu CPU %.6f RSS_KIB %ld STORED_NNZ %llu REDUCTIONS %llu\n",rank,targets.size(),(double)(clock()-start)/CLOCKS_PER_SEC,usage.ru_maxrss,(unsigned long long)final_nnz,(unsigned long long)reductions);
 for(uint32_t n=0;n<=12;n++)if(counts[n])printf("PIVOT degree=%u count=%u\n",n,counts[n]);return 0;
}
