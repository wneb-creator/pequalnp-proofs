extern "C" {
struct CCaDiCaL;
const char* ccadical_signature();
CCaDiCaL* ccadical_init();
void ccadical_release(CCaDiCaL*);
void ccadical_add(CCaDiCaL*,int);
void ccadical_assume(CCaDiCaL*,int);
int ccadical_solve(CCaDiCaL*);
int ccadical_val(CCaDiCaL*,int);
void ccadical_freeze(CCaDiCaL*,int);
void ccadical_set_option(CCaDiCaL*,const char*,int);
void ccadical_set_terminate(CCaDiCaL*,void*,int(*)(void*));
__attribute__((visibility("default"))) const char* search_signature(){return ccadical_signature();}
__attribute__((visibility("default"))) CCaDiCaL* search_init(){return ccadical_init();}
__attribute__((visibility("default"))) void search_release(CCaDiCaL*s){ccadical_release(s);}
__attribute__((visibility("default"))) void search_add(CCaDiCaL*s,int l){ccadical_add(s,l);}
__attribute__((visibility("default"))) void search_assume(CCaDiCaL*s,int l){ccadical_assume(s,l);}
__attribute__((visibility("default"))) int search_solve(CCaDiCaL*s){return ccadical_solve(s);}
__attribute__((visibility("default"))) int search_val(CCaDiCaL*s,int l){return ccadical_val(s,l);}
__attribute__((visibility("default"))) void search_freeze(CCaDiCaL*s,int l){ccadical_freeze(s,l);}
__attribute__((visibility("default"))) void search_set_option(CCaDiCaL*s,const char*n,int v){ccadical_set_option(s,n,v);}
__attribute__((visibility("default"))) void search_set_terminate(CCaDiCaL*s,void*p,int(*t)(void*)){ccadical_set_terminate(s,p,t);}
}
