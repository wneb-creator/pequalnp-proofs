#define main fullprobe_main
#include "signed-cached.cpp"
#undef main
#include <cassert>
int main(){
for(size_t i=0;i<rawInputs.size();i++)assert(intern(rawInputs[i],-1,-1,-1,int(i))==int(i));
for(auto&p:automorphisms){std::array<int,1024> rp;for(int r=0;r<1024;r++){int s=0;for(int i=0;i<10;i++)if(r>>p[i]&1)s|=1<<i;rp[r]=s;}rowPerms.push_back(rp);}
const std::vector<std::vector<std::array<int,3>>> circuits={{{{1,9,5}},{{1,0,9}},{{1,0,6}},{{1,7,3}},{{0,1,12}},{{1,6,5}},{{1,11,3}},{{1,13,1}},{{1,14,2}},{{0,12,15}},{{0,4,16}},{{0,19,11}},{{1,7,21}},{{0,18,17}},{{1,20,23}},{{1,3,15}},{{0,25,8}},{{0,22,10}},{{1,27,26}},{{1,24,28}}},{{{1,7,3}},{{1,1,5}},{{1,1,9}},{{1,3,6}},{{1,1,10}},{{1,5,9}},{{1,13,5}},{{0,11,0}},{{1,9,0}},{{1,18,3}},{{0,12,6}},{{0,2,14}},{{0,15,7}},{{0,8,16}},{{1,22,20}},{{0,4,19}},{{1,23,17}},{{1,21,26}},{{1,25,27}},{{1,24,28}}}};
for(size_t ci=0;ci<circuits.size();ci++){ auto&gs=circuits[ci];std::vector<int> bank;for(int i=0;i<10;i++)bank.push_back(i);std::vector<int> live=bank;std::vector<Step> prefix;
for(size_t j=0;j<gs.size();j++){int cap=20-j;auto g=gs[j];int a=bank[g[1]],b=bank[g[2]];auto ia=std::find(live.begin(),live.end(),a),ib=std::find(live.begin(),live.end(),b);assert(ia!=live.end()&&ib!=live.end()&&a!=b);int i=ia-live.begin(),q=ib-live.begin();
auto specs=makeSpecs(live,prefix,true,cap);Word zw=binary(g[0],wires[a].word,wires[b].word);int zi=intern(zw,g[0],a,b);assert(zw!=zero&&zw!=bneg(zero)&&std::find(live.begin(),live.end(),zi)==live.end());
bool ka=false,kb=false;for(size_t t=j+1;t<gs.size();t++){ka|=gs[t][1]==g[1]||gs[t][2]==g[1];kb|=gs[t][1]==g[2]||gs[t][2]==g[2];}
uint32_t deleted=(ka?0:1U<<i)|(kb?0:1U<<q);assert(live.size()+1-std::popcount(deleted)<=size_t(cap));Cov cov=wires[zi].cov;for(size_t t=0;t<live.size();t++)if(!(deleted>>t&1))cov=cor(cov,wires[live[t]].cov);assert(cov==covfull());
for(auto&s:specs){if(s.unavailable&~deleted)continue;auto&p=poolData[s.pool];int hi=p.bound+s.constants-std::popcount(s.constantmask&deleted),lo=cap-1+s.paid;if(lo>hi)continue;Word zr=band(zw,p.domain);bool constant=zr==zero||zr==p.domain;bool av=constant||contains(s.values,zr);if(lo+!av<hi+constant&&(av||!(s.unavailable&((1U<<i)|(1U<<q))))){std::cerr<<"false projection circuit="<<ci<<" gate="<<j<<" pool="<<s.pool<<std::endl;return 2;}}
CachedProfiles checker;assert(checker.build(live).first<0);std::vector<int> child;for(size_t t=0;t<live.size();t++)if(!(deleted>>t&1))child.push_back(live[t]);child.push_back(zi);assert(checker.child(deleted,zw)==collision(child));assert(checker.child(deleted,zw).first<0);live=child;prefix.push_back({g[0],a,b});bank.push_back(zi);
}assert(live.size()==1&&wires[live[0]].word==target);
for(int id:bank)for(size_t p=0;p<automorphisms.size();p++){int image=imageWire(id,p);for(int r=0;r<1024;r++)assert(bit(wires[image].word,r)==bit(wires[id].word,rowPerms[p][r]));}
std::cout<<"known circuit "<<ci<<": PASS20 steps, exact cached child collisions, all signed projection cuts, all120 DAGimages onall1024rows"<<std::endl;
}std::cout<<"PASS"<<std::endl;}
