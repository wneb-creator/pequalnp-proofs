#include <algorithm>
#include <cstdint>
#include <iostream>
#include <vector>
using Word=std::uint64_t;
std::vector<Word> closure(std::vector<Word> const& generators){
 std::vector<Word> ans{0};for(Word v:generators){std::size_t n=ans.size();for(std::size_t j=0;j<n;++j)ans.push_back(ans[j]|v);}
 std::sort(ans.begin(),ans.end());ans.erase(std::unique(ans.begin(),ans.end()),ans.end());return ans;
}
void solve(int n,bool square=false){
 std::vector<Word> inputs(n,0);for(int r=0;r<(1<<n);++r)for(int j=0;j<n;++j)if((r>>j)&1)inputs[j]|=Word(1)<<r;
 Word target=0;if(square)target=(inputs[0]|inputs[1])&(inputs[2]|inputs[3]);else for(int j=0;j<n;++j)target|=inputs[j]&inputs[(j+1)%n];
 auto clauses=closure(inputs);std::vector<Word> first;
 for(Word a:clauses)for(Word b:clauses)first.push_back(a&b);
 std::sort(first.begin(),first.end());first.erase(std::unique(first.begin(),first.end()),first.end());
 std::uint64_t tested=0;bool found=false;Word foundFirst=0,foundA=0,foundB=0;
 for(Word g:first){
  auto generators=inputs;generators.push_back(g);auto terms=closure(generators);
  Word supplied=0;for(Word v:generators)if((v&~target)==0)supplied|=v;
  if(supplied==target){found=true;foundFirst=g;break;}
  for(std::size_t i=0;i<terms.size()&&!found;++i)for(std::size_t j=i;j<terms.size();++j){
   ++tested;Word z=terms[i]&terms[j];if((z&~target)==0&&(supplied|z)==target){found=true;foundFirst=g;foundA=terms[i];foundB=terms[j];break;}
  }
  if(found)break;
 }
 std::cout<<"{\"n\":"<<n<<",\"graph\":\""<<(square?"K22":"cycle")<<"\",\"and_cap\":2,\"first_functions\":"<<first.size()<<",\"second_pairs\":"<<tested<<",\"found\":"<<(found?"true":"false")<<",\"witness\":["<<foundFirst<<","<<foundA<<","<<foundB<<"]}"<<std::endl;
}
void three_and_dual_five(){
 int n=5;std::vector<Word> inputs(n,0);for(int r=0;r<32;++r)for(int j=0;j<n;++j)if((r>>j)&1)inputs[j]|=Word(1)<<r;
 Word target=0;for(int r=0;r<32;++r){int z=31^r;bool edge=false;for(int j=0;j<5;++j)edge|=((z>>j)&(z>>((j+1)%5))&1);if(!edge)target|=Word(1)<<r;}
 auto clauses=closure(inputs);std::vector<Word> first;for(Word a:clauses)for(Word b:clauses)first.push_back(a&b);
 std::sort(first.begin(),first.end());first.erase(std::unique(first.begin(),first.end()),first.end());
 std::uint64_t seconds=0,thirds=0;bool found=false;Word fg=0,fh=0,fa=0,fb=0;
 for(Word g:first){
  if(std::binary_search(clauses.begin(),clauses.end(),g))continue;
  auto gens=inputs;gens.push_back(g);auto terms=closure(gens);std::vector<Word> second;
  for(std::size_t a=0;a<terms.size();++a)for(std::size_t b=a;b<terms.size();++b)second.push_back(terms[a]&terms[b]);
  std::sort(second.begin(),second.end());second.erase(std::unique(second.begin(),second.end()),second.end());
  for(Word h:second){
   ++seconds;auto gens2=gens;gens2.push_back(h);auto terms2=closure(gens2);Word supplied=0;
   for(Word v:gens2)if((v&~target)==0)supplied|=v;
   if(supplied==target){found=true;fg=g;fh=h;break;}
   for(std::size_t a=0;a<terms2.size()&&!found;++a)for(std::size_t b=a;b<terms2.size();++b){
    ++thirds;Word z=terms2[a]&terms2[b];if((z&~target)==0&&(supplied|z)==target){found=true;fg=g;fh=h;fa=terms2[a];fb=terms2[b];break;}
   }
   if(found)break;
  }
  if(found)break;
 }
 std::cout<<"{\"n\":5,\"graph\":\"dualC5\",\"and_cap\":3,\"second_functions\":"<<seconds<<",\"third_pairs\":"<<thirds<<",\"found\":"<<(found?"true":"false")<<",\"witness\":["<<fg<<","<<fh<<","<<fa<<","<<fb<<"]}"<<std::endl;
}
int main(){solve(4,true);solve(5);solve(6);three_and_dual_five();}
