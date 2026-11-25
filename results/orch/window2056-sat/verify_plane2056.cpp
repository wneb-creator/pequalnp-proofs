#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <vector>
using U=uint64_t;
struct Gate{int op,a,b;};
int main(int argc,char**argv){
 if(argc!=2)return 2;std::ifstream f(argv[1]);std::vector<Gate>gs;Gate g;
 while(f>>g.op>>g.a>>g.b){int n=26+gs.size();if((g.op!=0&&g.op!=1)||g.a<0||g.b<0||g.a>=n||g.b>=n)return 3;gs.push_back(g);}
 if(!f.eof())return 5;if(gs.empty())return 4;std::vector<U>v(26+gs.size());
 std::array<U,6>low={0xaaaaaaaaaaaaaaaaULL,0xccccccccccccccccULL,0xf0f0f0f0f0f0f0f0ULL,0xff00ff00ff00ff00ULL,0xffff0000ffff0000ULL,0xffffffff00000000ULL};
 for(uint32_t block=0;block<(1U<<20);block++){
  for(int i=0;i<6;i++)v[i]=low[i];for(int i=6;i<26;i++)v[i]=(block>>(i-6))&1?~U(0):U(0);
  for(int j=0;j<(int)gs.size();j++){auto h=gs[j];v[26+j]=h.op?(v[h.a]|v[h.b]):(v[h.a]&v[h.b]);}
  U target=0;for(int p=0;p<13;p++)for(int d: {0,1,3,9})target|=v[p]&v[13+(d+13-p)%13];
  if(v.back()!=target){std::cout<<"FAIL block="<<block<<" differingBits="<<(v.back()^target)<<"\n";return 1;}
 }
 std::cout<<"PASS all 67108864 assignments; gates="<<gs.size()<<"\n";return 0;
}
