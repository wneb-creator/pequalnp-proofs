#define main minimized_program_main
#include "exact_minimize_subgraph.cpp"
#undef main
int main(int argc,char**argv){
 if(argc!=2)return 2;std::ifstream f(argv[1]);int count;f>>count;
 for(int q=0;q<count;++q){Model m;int ns;f>>m.name>>m.n>>m.k>>m.rows>>ns>>m.target;
  m.inputs.resize(m.n);for(auto&x:m.inputs)f>>x;
  for(int s=0;s<ns;++s){int out;f>>out;for(int j=0;j<m.k+1;++j){Gate g;f>>g.op>>g.a>>g.b;}}
  prepare(m);int total=m.name=="theta"?(1<<m.edges.size()):128;
  for(int x=0;x<total;++x){U subset=m.name=="theta"?x:rng()&((U(1)<<m.edges.size())-1),h=0;
   for(size_t i=0;i<m.edges.size();++i)if(subset>>i&1)h|=U(1)<<m.edges[i][2];
   std::cout<<m.name<<' '<<h<<' '<<matching(m,h)<<'\n';}
 }
}
