#include <fstream>
#include <iostream>
#include <string>
#include <vector>
#include <cstdint>
#include <openf4.h>
int F4::VERBOSE=1;
int F4::NB_THREAD=1;
int main(int argc,char** argv) {
 if(argc!=2 || std::string(argv[1])=="--help") {
  std::cout<<"Usage: openf4_batch32 INPUT\nINPUT: prime n m, then n variable names, then m polynomial lines. Prime must be <=65521. Exact finite-field grevlex output, at most32 selected critical pairs per batch.\n";
  return argc==2?0:2;
 }
 std::ifstream in(argv[1]);int prime,n,m;in>>prime>>n>>m;
 if(!in || prime<3 || prime>65521 || n<1 || m<1)return 2;
 std::string *names=new std::string[n];for(int i=0;i<n;i++)in>>names[i];
 std::string line;std::getline(in,line);
 F4::Monomial::initMonomial(n);F4::Monomial::setVariable(names);
 using Field=F4::ElementPrime<int32_t>;
 Field::setModulo(prime);
 std::vector<F4::Polynomial<Field>> polys;
 for(int i=0;i<m;i++){if(!std::getline(in,line))return 3;polys.emplace_back(line);}
 F4::Ideal<Field> ideal(polys,n);ideal.f4();
 auto basis=ideal.getReducedGroebnerBasis();
 std::cout<<"BASIS "<<basis.size()<<"\n";
 for(auto &s:basis)std::cout<<s<<"\n";
 return 0;
}
