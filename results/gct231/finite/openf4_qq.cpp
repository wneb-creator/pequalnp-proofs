#include <gmpxx.h>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>
#include <stdexcept>
namespace F4 {
class ElementRational {
public:
 mpq_class _element;
 static long getModulo(){return 0;}
 static long getMax(){return 0;}
 const mpq_class& modulo(){_element.canonicalize();return _element;}
 const mpq_class& getElement()const{return _element;}
 ElementRational& addMult(const ElementRational& a,const ElementRational& b){_element+=a._element*b._element;return *this;}
 ElementRational& inverse(){if(_element==0)throw std::domain_error("zero inverse");_element=1/_element;return *this;}
 bool isZero()const{return _element==0;}
 bool isOne()const{return _element==1;}
 void setZero(){_element=0;}
 void setOne(){_element=1;}
 ElementRational& operator=(long x){_element=x;return *this;}
 ElementRational& operator=(const mpq_class& x){_element=x;return *this;}
 ElementRational& operator*=(const ElementRational& x){_element*=x._element;return *this;}
 ElementRational& operator-=(const ElementRational& x){_element-=x._element;return *this;}
};
std::ostream& operator<<(std::ostream& out,const ElementRational& x){return out<<x._element;}
ElementRational operator*(ElementRational a,const ElementRational& b){a*=b;return a;}
ElementRational operator-(ElementRational a){a._element=-a._element;return a;}
}
#include <openf4.h>
namespace F4 {
template<> void Term<ElementRational>::readCoefficient(std::string const text){
 size_t end=text.find('*');std::string coeff=text.substr(0,end);
 size_t prefix=0;if(!coeff.empty() && (coeff[0]=='+' || coeff[0]=='-'))prefix=1;
 if(prefix==coeff.size() || !std::isdigit(coeff[prefix])){_coefficient=(text[0]=='-'?-1L:1L);return;}
 if(coeff[0]=='+')coeff.erase(0,1);
 _coefficient._element=mpq_class(coeff);_coefficient._element.canonicalize();
}
}
int F4::VERBOSE=0;
int F4::NB_THREAD=1;
int main(int argc,char** argv){
 if(argc!=2 || std::string(argv[1])=="--help"){
  std::cout<<"Usage: openf4_qq INPUT\nInput: 0 n m, variable names, then signed integer polynomial lines. Exact QQ grevlex output.\n";return argc==2?0:2;
 }
 std::ifstream in(argv[1]);int characteristic,n,m;in>>characteristic>>n>>m;
 if(!in || characteristic!=0 || n<1 || m<1)return 2;
 auto names=new std::string[n];for(int i=0;i<n;i++)in>>names[i];
 std::string line;std::getline(in,line);
 F4::Monomial::initMonomial(n);F4::Monomial::setVariable(names);
 std::vector<F4::Polynomial<F4::ElementRational>> polys;
 for(int i=0;i<m;i++){if(!std::getline(in,line))return 3;polys.emplace_back(line);}
 F4::Ideal<F4::ElementRational> ideal(polys,n);ideal.f4();
 auto basis=ideal.getReducedGroebnerBasis();
 std::cout<<"BASIS "<<basis.size()<<"\n";
 for(auto &poly:basis)std::cout<<poly<<"\n";
}
