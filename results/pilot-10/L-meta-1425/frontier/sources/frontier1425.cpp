#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <string>
#include <unordered_set>
#include <vector>
using W=uint32_t;using State=std::vector<W>;
struct Hash{size_t operator()(State const&s)const{uint64_t h=123417;for(W w:s)h^=w+0x9e3779b97f4a7c15ULL+(h<<6)+(h>>2);return h;}};
int main(int argc,char**argv){
 if(argc!=6){std::cerr<<"usage: frontier1425 targethex budget limit prefix mode\n";return 2;}
 W target=std::stoul(argv[1],nullptr,16);int budget=std::stoi(argv[2]);size_t limit=std::stoull(argv[3]);std::string prefix=argv[4],mode=argv[5];
 State initial={0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000};std::sort(initial.begin(),initial.end());
 std::vector<std::pair<int,int>>pairs;for(int i=0;i<32;i++)if(!(target>>i&1))for(int j=0;j<32;j++)if(target>>j&1)pairs.push_back({i,j});
 auto covered=[&](State const&ws,int s){
  bool directed=mode=="tight"&&int(ws.size())==s+1;
  if(directed){for(auto[i,j]:pairs){bool ok=false;for(W w:ws)if(!(w>>i&1)&&(w>>j&1)){ok=true;break;}if(!ok)return false;}return true;}
  std::array<unsigned char,1024> seen{};
  for(int x=0;x<32;x++){unsigned code=0;for(int i=0;i<int(ws.size());i++)code|=((ws[i]>>x)&1)<<i;unsigned v=1u<<((target>>x)&1);if(seen[code]&&seen[code]!=v)return false;seen[code]=v;}return true;
 };
 std::unordered_set<State,Hash>cur,next;cur.insert(initial);uint64_t candidates=0,rejected=0;auto start=std::chrono::steady_clock::now();
 std::ofstream meta(prefix+".meta.json");meta<<"{\"target\":"<<target<<",\"budget\":"<<budget<<",\"mode\":\""<<mode<<"\",\"inputs\":[2863311530,3435973836,4042322160,4278255360,4294901760]}\n";
 for(int s=budget;s>=0;s--){
  std::cout<<"remaining="<<s<<" states="<<cur.size()<<" candidates="<<candidates<<" rejected="<<rejected<<" seconds="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<std::endl;
  std::vector<State>ordered(cur.begin(),cur.end());std::sort(ordered.begin(),ordered.end());std::ofstream out(prefix+".layer"+std::to_string(s)+".jsonl");for(auto const&ws:ordered){out<<'[';for(size_t i=0;i<ws.size();i++){if(i)out<<',';out<<ws[i];}out<<"]\n";}out.close();
  if(s==0){bool sat=cur.count(State{target});std::cout<<(sat?"SURVIVING_GOAL":"EXHAUSTED")<<std::endl;return sat?10:0;}
  next.clear();if(s-1>=4)next.insert(initial);bool over=false;
  auto add=[&](State ws){candidates++;if(ws.size()>size_t(s)||!covered(ws,s-1)){rejected++;return;}std::sort(ws.begin(),ws.end());next.insert(std::move(ws));if(next.size()>limit)over=true;};
  for(auto const&ws:ordered){int width=ws.size(),slack=s+1-width;
   for(int i=0;i<width;i++){
    if(slack>=1){State w=ws;w[i]^=0xffffffffu;add(w);}
    if(slack>=2){State w=ws;w.push_back(~ws[i]);add(w);}
    for(int j=i+1;j<width;j++)for(int op=0;op<2;op++)for(int keep=0;keep<4;keep++){
     int saves=(keep&1)+((keep>>1)&1);if(slack<saves)continue;State w;w.push_back(op?(ws[i]|ws[j]):(ws[i]&ws[j]));for(int z=0;z<width;z++)if(z!=i&&z!=j)w.push_back(ws[z]);if(keep&1)w.push_back(ws[i]);if(keep&2)w.push_back(ws[j]);add(std::move(w));
    }
   }
   if(over){std::cout<<"STATE_CAP remaining="<<s-1<<" partial="<<next.size()<<std::endl;return 11;}
  }cur.swap(next);
 }
}
