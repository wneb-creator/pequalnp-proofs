#define main original_main
#include "signed-cached.cpp"
#undef main
#include <cassert>
#include <random>
int main(){
 std::mt19937_64 random(2373);uint64_t checked=0;
 for(int test=0;test<12;test++){
  std::vector<int> parent;for(auto&w:rawInputs)parent.push_back(intern(w));
  int width=10+test%10;
  while(int(parent.size())<width){Word w;for(auto&part:w)part=random();parent.push_back(intern(w));}
  std::shuffle(parent.begin(),parent.end(),random);
  CachedProfiles profiles;assert(profiles.build(parent)==collision(parent));assert(collision(parent).first<0);
  for(int i=0;i<width;i++)for(int j=i+1;j<width;j++)for(int op=0;op<4;op++){
   Word output=binary(op,wires[parent[i]].word,wires[parent[j]].word);int result=intern(output,op,parent[i],parent[j]);
   for(int keeps=0;keeps<4;keeps++){
    uint32_t deleted=(keeps&1?0:1U<<i)|(keeps&2?0:1U<<j);
    std::vector<int> child;for(int k=0;k<width;k++)if(!(deleted>>k&1))child.push_back(parent[k]);child.push_back(result);std::shuffle(child.begin(),child.end(),random);
    assert(profiles.child(deleted,output)==collision(child));checked++;
   }
  }
 }
 // The wraparound branch must clear old stamps before reusing stamp one.
 std::vector<int> parent;for(auto&w:rawInputs)parent.push_back(intern(w));
 CachedProfiles profiles;CachedProfiles::stamp=UINT32_MAX;assert(profiles.build(parent).first<0);
 Word output=band(wires[parent[0]].word,wires[parent[1]].word);int result=intern(output);
 std::vector<int> child{result};for(int i=2;i<10;i++)child.push_back(parent[i]);
 CachedProfiles::stamp=UINT32_MAX;assert(profiles.child(3,output)==collision(child));
 std::cout<<"PASS synthetic_parents=12 widths=10..19 randomized_child_order comparisons="<<checked<<" stamp_wrap_tests=2"<<std::endl;
}
