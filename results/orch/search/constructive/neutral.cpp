#define main old_main
#include "search.cpp"
#undef main

using BigCircuit = std::array<Gate,54>;
std::vector<int> falsepairs;
std::array<std::array<U,2>,14> pairinputs;
U bigeval(const BigCircuit &c) {
  U wires[68]; for(int i=0;i<14;i++)wires[i]=inputs[i];
  for(int i=0;i<54;i++){ const auto &g=c[i];wires[14+i]=g.land?wires[g.a]&wires[g.b]:wires[g.a]|wires[g.b]; }
  return wires[67];
}
U active(const BigCircuit &c) {
  U mask=U(1)<<53;
  for(int i=53;i>=0;i--)if(mask>>i&1)for(int w:{c[i].a,c[i].b})if(w>=14)mask|=U(1)<<(w-14);
  return mask;
}
int dirtyands(const BigCircuit &c) {
  U mask=active(c);std::array<U,2>wires[68];for(int i=0;i<14;i++)wires[i]=pairinputs[i];int dirty=0;
  for(int i=0;i<54;i++){
    const auto&g=c[i];for(int part=0;part<2;part++)wires[14+i][part]=g.land?wires[g.a][part]&wires[g.b][part]:wires[g.a][part]|wires[g.b][part];
    if((mask>>i&1)&&g.land&&(wires[14+i][0]||wires[14+i][1]))dirty++;
  }
  return dirty;
}
void normalize(BigCircuit &c) {
  U wires[68];int alias[68];
  for(int i=0;i<14;i++){wires[i]=inputs[i];alias[i]=i;}
  for(int i=0;i<54;i++){
    auto&g=c[i];g.a=alias[g.a];g.b=alias[g.b];
    U value=g.land?wires[g.a]&wires[g.b]:wires[g.a]|wires[g.b];
    wires[14+i]=value;alias[14+i]=14+i;
    for(int j=0;j<14+i;j++)if(alias[j]==j){
      U other=wires[j];
      if(!(value&target&~other)&&!(other&~target&~value)){alias[14+i]=j;break;}
    }
  }
  if(alias[67]!=67){
    int j=alias[67];
    if(j<14){std::cerr<<"unexpected input output\n";std::exit(4);}
    c[53]=c[j-14];
  }
}
BigCircuit bigseed() {
  std::vector<Gate> gates;
  std::vector<int> terms,order={0,1,2,3,4,5,6};
  std::shuffle(order.begin(),order.end(),rng);bool reverse=rnd(2);
  for(int i:order){
    int v=i+(reverse?7:0);std::vector<int>ns;
    for(auto[a,b]:edges){if(a==v)ns.push_back(b);if(b==v)ns.push_back(a);}
    std::shuffle(ns.begin(),ns.end(),rng);
    gates.push_back({ns[0],ns[1],false});
    gates.push_back({14+int(gates.size())-1,ns[2],false});
    gates.push_back({v,14+int(gates.size())-1,true});
    terms.push_back(14+int(gates.size())-1);
  }
  while(terms.size()>1){int a=rnd(terms.size());int v=terms[a];terms.erase(terms.begin()+a);int b=rnd(terms.size());int w=terms[b];terms.erase(terms.begin()+b);gates.push_back({v,w,false});terms.push_back(14+int(gates.size())-1);}
  auto remap=[](int w){return w<14?w:14+2*(w-14)+1;};
  BigCircuit c;
  for(int i=0;i<27;i++){
    c[2*i]={rnd(14+2*i),rnd(14+2*i),bool(rnd(2))};
    c[2*i+1]={remap(gates[i].a),remap(gates[i].b),gates[i].land};
  }
  return c;
}
void bigwrite(const BigCircuit&c,const std::string&path){
  U mask=active(c);int wires[68];for(int i=0;i<14;i++)wires[i]=i;int count=0;std::ofstream out(path);out<<"[\n";
  for(int i=0;i<54;i++)if(mask>>i&1){wires[14+i]=14+count++;out<<"["<<wires[c[i].a]<<","<<wires[c[i].b]<<",\""<<(c[i].land?"and":"or")<<"\"]"<<(i==53?"\n":",\n");}
  out<<"]\n";
}
int main(int argc,char**argv){
  int seconds=argc>1?std::stoi(argv[1]):600;std::string prefix=argc>2?argv[2]:"neutral";if(argc>3)rng.seed(std::stoull(argv[3]));
  for(auto[a,b]:edges)rows.push_back((1<<a)|(1<<b));
  for(int mask=0;mask<(1<<14);mask++)if(isfalse(mask)){bool maximal=true;for(int i=0;i<14;i++)if(!(mask>>i&1)&&isfalse(mask|(1<<i))){maximal=false;break;}if(maximal)rows.push_back(mask);}
  if(rows.size()>64)return 2;
  for(size_t r=0;r<rows.size();r++)for(int i=0;i<14;i++)if(rows[r]>>i&1)inputs[i]|=U(1)<<r;
  target=(U(1)<<21)-1;
  for(int mask=0;mask<(1<<14);mask++)if(std::popcount(unsigned(mask))<=2&&isfalse(mask))falsepairs.push_back(mask);
  for(size_t r=0;r<falsepairs.size();r++)for(int i=0;i<14;i++)if(falsepairs[r]>>i&1)pairinputs[i][r/64]|=U(1)<<(r%64);
  std::cout<<"rows="<<rows.size()<<" budget_seconds="<<seconds<<std::endl;
  auto start=std::chrono::steady_clock::now();double nextreport=0;U iterations=0,accepted=0,changes=0;int restarts=0,best=100,mostdirty=0;
  while(true){
    BigCircuit current=bigseed();int cost=std::popcount(active(current));
    if(bigeval(current)!=target){std::cerr<<"bad seed\n";return 3;}
    for(int k=0;k<5000000;k++,iterations++){
      BigCircuit next=current;int times=1+(rnd(100)<15)+(rnd(100)<4);U oldactive=active(current);
      for(int j=0;j<times;j++){int i=rnd(54),type=rnd(10);if(type==0)next[i].land=!next[i].land;else if(type<5)next[i].a=rnd(14+i);else next[i].b=rnd(14+i);}
      if(bigeval(next)==target){
        if(iterations%128==0){normalize(next);if(bigeval(next)!=target){std::cerr<<"normalization failed\n";return 5;}}
        int nc=std::popcount(active(next));
        if(nc<best){best=nc;bigwrite(next,prefix+"-best.json");std::cout<<"best="<<best<<" iterations="<<iterations<<std::endl;}
        if(nc<=26){bigwrite(next,prefix+"-solution.json");std::cout<<"FOUND\n";return 0;}
        double temps[]={0.0,0.25,0.5,1.0};double temp=temps[restarts%4];
        if(nc<=32&&(nc<=cost || (temp>0&&double(rng())/double(UINT64_MAX)<std::exp(double(cost-nc)/temp)))){
          for(int i=0;i<54;i++)if((oldactive>>i&1)&&(next[i].a!=current[i].a||next[i].b!=current[i].b||next[i].land!=current[i].land)){changes++;break;}
          current=next;cost=nc;accepted++;
          if(nc==27&&iterations%16==0){int dirty=dirtyands(next);if(dirty>mostdirty){mostdirty=dirty;bigwrite(next,prefix+"-dirty-"+std::to_string(dirty)+".json");std::cout<<"dirty_ands="<<dirty<<" iterations="<<iterations<<std::endl;}}
        }
      }
      if(k%4096==0){double elapsed=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
        if(elapsed>=seconds){std::cout<<"DONE iterations="<<iterations<<" restarts="<<restarts<<" best="<<best<<" accepted="<<accepted<<" active_changes="<<changes<<std::endl;return 1;}
        if(elapsed>=nextreport){std::cout<<"progress seconds="<<elapsed<<" iterations="<<iterations<<" restarts="<<restarts<<" best="<<best<<" active_changes="<<changes<<std::endl;nextreport=elapsed+30;}
      }
    }
    restarts++;
  }
}
