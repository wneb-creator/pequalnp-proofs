#define main search_main
#include "eight2056_local.cpp"
#undef main
int main(int argc,char**argv){
 if(argc!=2)return 2;std::ifstream f(argv[1]);Data d;int points,budget,pos,neg;f>>d.inputs>>points>>budget>>pos>>neg;
 for(int k=0;k<pos+neg;k++){int r;f>>r;d.rows.push_back(r);int word=k/64,bit=k%64;for(int i=0;i<d.inputs;i++)if((r>>i)&1)d.val[i][word]|=U(1)<<bit;if(k<pos){d.target[word]|=U(1)<<bit;d.edges.push_back({std::countr_zero((unsigned)r),std::countr_zero((unsigned)(r&(r-1)))});}else d.negative[word]|=U(1)<<bit;d.mask[word]|=U(1)<<bit;}
 std::mt19937 rng(2056008);int checked=0;
 for(int trial=0;trial<60000;trial++){
  Net c;if(trial%2)c=deleted(d,star(d,rng,true),rng);else for(int j=0;j<GATES;j++)c[j]={int(rng()%2),int(rng()%(d.inputs+j)),int(rng()%(d.inputs+j))};
  if(trial%2)mutate(d,c,rng,1+rng()%8);if(!valid(d,c))continue;
  auto v=d.val;for(int j=0;j<GATES;j++){auto g=c[j];for(int k=0;k<WORDS;k++)v[d.inputs+j][k]=g.op?(v[g.a][k]|v[g.b][k]):(v[g.a][k]&v[g.b][k]);}Bits before=v[d.inputs+GATES-1];
  int score=eval(d,c,trial%2);if(d.raw==0){show(d,c,score,trial%2,0);return 0;}if(!valid(d,c))return 3;
  v=d.val;for(int j=0;j<GATES;j++){auto g=c[j];for(int k=0;k<WORDS;k++)v[d.inputs+j][k]=g.op?(v[g.a][k]|v[g.b][k]):(v[g.a][k]&v[g.b][k]);}Bits after=v[d.inputs+GATES-1];
  if(after!=d.val[d.inputs+GATES-1])return 4;
  for(int k=0;k<WORDS;k++){
   if((before[k]&d.target[k]&~after[k])!=0)return 5;
   if((after[k]&d.negative[k]&~before[k])!=0)return 6;
  }
  checked++;
 }
 std::cout<<"PASS "<<checked<<" valid nets from 60000 randomized trials; three-word dominance checks: no lost positives, no new negatives, actual mutated nets match evaluator, backward reads preserved"<<std::endl;
 return 0;
}
