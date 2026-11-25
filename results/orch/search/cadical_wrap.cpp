extern "C" {
void *ccadical_init();
void ccadical_add(void *, int);
void ccadical_assume(void *, int);
void ccadical_freeze(void *, int);
int ccadical_solve(void *);
int ccadical_val(void *, int);
void ccadical_set_option(void *, const char *, int);
void ccadical_limit(void *, const char *, int);
void ccadical_release(void *);
void ccadical_set_terminate(void *, void *, int (*)(void *));
void *sat_init() { return ccadical_init(); }
void sat_add(void *s,int v) { ccadical_add(s,v); }
void sat_assume(void *s,int v) { ccadical_assume(s,v); }
void sat_freeze(void *s,int v) { ccadical_freeze(s,v); }
int sat_solve(void *s) { return ccadical_solve(s); }
int sat_val(void *s,int v) { return ccadical_val(s,v); }
void sat_set_option(void *s,const char *k,int v) { ccadical_set_option(s,k,v); }
void sat_limit(void *s,const char *k,int v) { ccadical_limit(s,k,v); }
void sat_release(void *s) { ccadical_release(s); }
void sat_set_terminate(void *s,void *p,int (*f)(void *)) { ccadical_set_terminate(s,p,f); }
}
