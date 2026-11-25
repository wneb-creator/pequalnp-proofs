#define main prior_main
#include "/tmp/oec/pequalnp-pilot-92/local-search.cpp"
#undef main
int main(int argc,char**argv) {
  int maxseeds=argc>1?atoi(argv[1]):20;
  const int edges[15][2]={{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}};
  for(int x=0;x<1024;x++) {
    uint64_t bit=uint64_t(1)<<(x%64);int k=x/64;
    for(int i=0;i<10;i++)if(x>>i&1)base[i][k]|=bit;
    bool f=false;for(auto e:edges)f|=(x>>e[0]&1)&&(x>>e[1]&1);
    if(f)goal[k]|=bit;else negative[k]|=bit;
    if(__builtin_popcount((unsigned)x)<=3)low[k]|=bit;
  }
  vector<pair<int,Circ>> seeds;
  for(int d=0;d<20;d++)for(int r=0;r<10+d;r++) {auto c=seed(d,r);seeds.push_back({score(c),c});}
  sort(seeds.begin(),seeds.end(),[](auto&a,auto&b){return a.first<b.first;});
  int best=100000;
  auto start=chrono::steady_clock::now();
  for(int k=0;k<min(maxseeds,(int)seeds.size());k++) {
    Circ s=seeds[k].second;
    for(int i=0;i<19;i++)for(int a=0;a<10+i;a++) {
      Circ c=s;c.g[i]={2,a,0};
      for(int j=0;j<19;j++)if(i!=j) {
        Gate old=c.g[j];
        for(int op=0;op<3;op++)for(int b=0;b<10+j;b++)for(int d=op==2?b:0;d<=(op==2?b:b);d++) {
          c.g[j]={op,b,d};int val=score(c);
          if(val<best) {
            best=val;int raw;score(c,&raw);
            cerr<<"best "<<best<<" raw "<<raw<<" seed "<<k<<" notGate "<<i<<" secondGate "<<j<<" evals "<<evaluations<<endl;
            dump(c,best,"/tmp/oec/pequalnp-pilot-92/local-twoedit-best.txt");
            if(best==0){cerr<<"FOUND"<<endl;return 0;}
          }
        }
        c.g[j]=old;
      }
    }
    cerr<<"seed_done "<<k<<" best "<<best<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<endl;
  }
  cerr<<"done best "<<best<<" evals "<<evaluations<<endl;
  return 1;
}
