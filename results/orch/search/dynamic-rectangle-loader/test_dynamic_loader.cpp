#define main archived_search_main
#include "copy_dynamic_test_unit.cpp"
#undef main
#include <cassert>
int main(int argc,char**argv){
 assert(argc==2);string dir=argv[1],one=dir+"/one.txt";
 vector<string>args={"test","--cap","19","--nodes","0","--seconds","0","--extra-rectangles",one};vector<char*>ptrs;for(auto&s:args)ptrs.push_back(s.data());
 assert(archived_search_main(ptrs.size(),ptrs.data())==0);assert(extraRectangles.size()==1);
 extra_rectangle_cost(extraRectangles[0],inputs[0]);auto oldCache=extraRectangles[0].profiles;
 extraRectPath=dir+"/six.txt";lastExtraLoad={};maybe_load_extra_rectangles();assert(extraRectangles.size()==6);assert(extraRectangles[0].profiles==oldCache);
 ifstream names(dir+"/invalid-list.txt");string name;int rejected=0;
 while(names>>name){auto before=extraRectangles.size();vector<vector<long long>>identities;for(auto&e:extraRectangles)identities.push_back(e.identity);extraRectPath=dir+"/"+name+".txt";lastExtraLoad={};maybe_load_extra_rectangles();assert(extraRectangles.size()==before);for(size_t i=0;i<before;i++)assert(extraRectangles[i].identity==identities[i]);rejected++;}
 ifstream data(dir+"/costs.txt");int n;assert(bool(data>>n));int comparisons=0,cuts=0;
 for(int t=0;t<n;t++){int mid,count;assert(bool(data>>mid>>count));auto it=find_if(extraRectangles.begin(),extraRectangles.end(),[&](auto&e){return e.id==mid;});assert(it!=extraRectangles.end());vector<int>state;long long sum=0;
  for(int i=0;i<count;i++){string hex;long long expected;assert(bool(data>>hex>>expected));int id=intern(memo_word(hex));auto got=extra_rectangle_cost(*it,id);assert(got==expected);sum+=got;state.push_back(id);comparisons++;}
  assert(sum<it->total);assert(extra_rectangle_cut(state));cuts++;
 }
 cout<<"dynamic loader tests PASS rejected="<<rejected<<" append_count="<<extraRectangles.size()<<" root_costs="<<comparisons<<" exact_cuts="<<cuts<<" preserved_existing_cache=1"<<endl;
}
