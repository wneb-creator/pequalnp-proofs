#define FORCE_WIRE_HASH_COLLISIONS
#define main unused_signed_main
#include "signed-hash.cpp"
#undef main
#include <cassert>
int main(){
 for(int i=0;i<10;i++)assert(intern(rawInputs[i],-1,-1,-1,i)==i);
 std::vector<Word> examples;
 for(unsigned i=0;i<2000;i++){Word w{};w[0]=2ULL*(i+1);examples.push_back(w);assert(intern(w)==int(10+i));}
 for(int i=1999;i>=0;i--){assert(intern(examples[i])==10+i);assert(lookupWire(examples[i])==10+i);}
 Word missing{};missing[0]=1000000;assert(lookupWire(missing)==-1);
 assert(wireHashIds.count(0)==wires.size());
 std::vector<int> bank;for(int i=0;i<10;i++)bank.push_back(i);std::vector<Step> prefix;
 const std::vector<std::array<int,3>> gates={{{1,9,5}},{{1,0,9}},{{1,0,6}},{{1,7,3}},{{0,1,12}},{{1,6,5}},{{1,11,3}},{{1,13,1}},{{1,14,2}},{{0,12,15}},{{0,4,16}},{{0,19,11}},{{1,7,21}},{{0,18,17}},{{1,20,23}},{{1,3,15}},{{0,25,8}},{{0,22,10}},{{1,27,26}},{{1,24,28}}};
 for(size_t j=0;j<gates.size();j++){auto g=gates[j];int a=bank[g[1]],b=bank[g[2]];int id=intern(binary(g[0],wires[a].word,wires[b].word),g[0],a,b);bank.push_back(id);if(j+1==gates.size()){assert(wires[id].word==target);writeTarget(prefix,g[0],a,b);}prefix.push_back({g[0],a,b});}
 for(size_t i=0;i<wires.size();i++)assert(lookupWire(wires[i].word)==int(i));
 std::cout<<"PASS forced-zero hash:2000 distinct words, repeated and absent lookups, vector growth, known20 target DAG emission; entries="<<wires.size()<<std::endl;
}
