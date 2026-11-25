#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <set>
#include <sstream>
#include <string>
#include <vector>

struct Gate { bool isOr;unsigned a,b; };
constexpr std::array<unsigned,13> incidence={1170,113,2584,4372,15,4674,2338,7169,1352,1572,897,2244,4264};
bool evaluate(const std::vector<Gate>&g,unsigned n,unsigned output,unsigned mask) {
    std::vector<bool> w;for(unsigned i=0;i<n;i++)w.push_back((mask>>i)&1);
    for(auto h:g)w.push_back(h.isOr?(w[h.a]||w[h.b]):(w[h.a]&&w[h.b]));
    return w.at(output);
}
int main(int argc,char**argv) {
    if(argc<4){std::cerr<<"usage: map.txt core-gates.txt output.txt [allow64]\n";return 2;}
    bool allow64=argc>4&&std::string(argv[4])=="allow64";
    std::ifstream mapFile(argv[1]);unsigned k,n,goal;mapFile>>k>>n>>goal;
    if(!mapFile||k<1||k>13||n<k||n>26||goal!=5*k-2)return 2;
    std::vector<unsigned> points(k),mapping(n);
    for(auto &p:points)mapFile>>p;for(auto &p:mapping)mapFile>>p;
    if(!mapFile||std::set<unsigned>(mapping.begin(),mapping.end()).size()!=n)return 2;
    for(unsigned i=0;i<k;i++)if(points[i]>=13||mapping[i]!=points[i])return 2;
    for(unsigned i=k;i<n;i++)if(mapping[i]<13||mapping[i]>=26)return 2;
    for(auto p:points)for(unsigned l=0;l<13;l++)if((incidence[p]>>l)&1) {
        bool present=false;for(unsigned i=k;i<n;i++)present|=mapping[i]==13+l;
        if(!present)return 2;
    }
    std::ifstream input(argv[2]);std::string line;std::vector<Gate> core;
    while(std::getline(input,line)) {
        std::istringstream row(line);unsigned number,a,b;std::string op;
        if(!(row>>number>>op>>a>>b))continue;
        if(op!="and"&&op!="or")continue;
        if(number!=n+core.size()||a>=number||b>=number)return 2;
        core.push_back({op=="or",a,b});
    }
    if(core.empty()||core.size()>goal+(allow64?1:0))return 2;
    auto remap=[&](unsigned v){return v<n?mapping[v]:26+v-n;};
    std::vector<Gate> full;for(auto h:core)full.push_back({h.isOr,remap(h.a),remap(h.b)});
    std::vector<unsigned> outputs={26+unsigned(core.size())-1};
    auto add=[&](bool isOr,unsigned a,unsigned b){full.push_back({isOr,a,b});return 25+unsigned(full.size());};
    for(unsigned p=0;p<13;p++) {
        if(std::set<unsigned>(points.begin(),points.end()).contains(p))continue;
        std::vector<unsigned> neighbors;for(unsigned l=0;l<13;l++)if((incidence[p]>>l)&1)neighbors.push_back(13+l);
        unsigned v=neighbors[0];for(unsigned i=1;i<neighbors.size();i++)v=add(true,v,neighbors[i]);
        outputs.push_back(add(false,p,v));
    }
    unsigned output=outputs[0];for(unsigned i=1;i<outputs.size();i++)output=add(true,output,outputs[i]);
    if(full.size()>63+(allow64?1:0)||output!=25+full.size())return 2;
    unsigned trueChecks=0,closedChecks=0;
    for(unsigned p=0;p<13;p++)for(unsigned l=0;l<13;l++)if((incidence[p]>>l)&1) {
        if(!evaluate(full,26,output,(1u<<p)|(1u<<(13+l)))){std::cerr<<"failed edge "<<p<<" "<<l<<"\n";return 1;}
        trueChecks++;
    }
    for(unsigned P=0;P<(1u<<13);P++) {
        unsigned L=(1u<<13)-1;for(unsigned p=0;p<13;p++)if((P>>p)&1)L&=~incidence[p];
        if(evaluate(full,26,output,P|(L<<13))){std::cerr<<"failed negative closure "<<P<<" "<<L<<"\n";return 1;}
        unsigned closure=0;for(unsigned p=0;p<13;p++)if(!(incidence[p]&L))closure|=1u<<p;
        if(closure==P)closedChecks++;
    }
    if(trueChecks!=52||closedChecks!=704)return 2;
    std::ofstream out(argv[3]);out<<"gates "<<full.size()<<" output "<<output<<"\n";
    for(unsigned i=0;i<full.size();i++)out<<26+i<<" "<<(full[i].isOr?"or":"and")<<" "<<full[i].a<<" "<<full[i].b<<"\n";
    out.flush();if(!out.good())return 2;
    std::cout<<"VALID: "<<full.size()<<" AND/OR gates;52 edge rows,704 maximal false rows,and all8192negativeclosures checked\n";
    return 0;
}
