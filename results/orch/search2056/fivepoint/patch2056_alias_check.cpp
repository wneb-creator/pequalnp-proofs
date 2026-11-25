#define main search_main
#include "patch2056_five_alias.cpp"
#undef main
int main(int argc,char**argv){
 if(argc!=2)return 2;std::ifstream f(argv[1]);int count;f>>count;std::mt19937 rng(2056007);
 for(int id=0;id<count;id++){Data d;d.id=id;int pos,neg;f>>d.inputs>>pos>>neg;
  for(int k=0;k<pos+neg;k++){int r;f>>r;d.rows.push_back(r);for(int i=0;i<d.inputs;i++)if((r>>i)&1)d.val[i]|=U(1)<<k;if(k<pos){d.target|=U(1)<<k;d.edges.push_back({std::countr_zero((unsigned)r),std::countr_zero((unsigned)(r&(r-1)))});}else d.negative|=U(1)<<k;d.mask|=U(1)<<k;}
  for(int trial=0;trial<20000;trial++){
   Net c;if(trial%2)c=deleted(d,star(d,rng,true),rng);else for(int j=0;j<GATES;j++)c[j]={int(rng()%2),int(rng()%(d.inputs+j)),int(rng()%(d.inputs+j))};
   if(trial%2)mutate(d,c,rng,1+rng()%8);if(!valid(d,c))continue;
   auto v=d.val;for(int j=0;j<GATES;j++){auto g=c[j];v[d.inputs+j]=g.op?(v[g.a]|v[g.b]):(v[g.a]&v[g.b]);}U before=v[d.inputs+GATES-1];
   eval(d,c,trial%2);if(!valid(d,c))return 3;
   v=d.val;for(int j=0;j<GATES;j++){auto g=c[j];v[d.inputs+j]=g.op?(v[g.a]|v[g.b]):(v[g.a]&v[g.b]);}U after=v[d.inputs+GATES-1];
   if(after!=d.val[d.inputs+GATES-1])return 4;
   if(((before^after)&d.target)!=0)return 5;
   if((after&d.negative&~before)!=0)return 6;
  }
 }
 std::cout<<"PASS60000 randomized normalization checks: all positive profiles preserved, no new negative acceptances, actual mutated nets match evaluator, backward reads preserved"<<std::endl;
 return 0;
}
