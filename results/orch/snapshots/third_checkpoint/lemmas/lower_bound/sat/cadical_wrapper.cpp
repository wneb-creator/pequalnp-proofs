// Minimal ABI bridge to the bundled CaDiCaL 2.1.2 C API.
// Signatures checked against github.com/arminbiere/cadical,
// rel-2.1.2/src/ccadical.h on 2026-11-25.
extern "C" {
struct CCaDiCaL;
CCaDiCaL *ccadical_init();
void ccadical_release(CCaDiCaL *);
void ccadical_add(CCaDiCaL *, int);
void ccadical_assume(CCaDiCaL *, int);
void ccadical_freeze(CCaDiCaL *, int);
int ccadical_solve(CCaDiCaL *);
int ccadical_val(CCaDiCaL *, int);
void ccadical_set_option(CCaDiCaL *, const char *, int);
void ccadical_set_terminate(CCaDiCaL *, void *, int (*)(void *));

CCaDiCaL *pilot_init() { return ccadical_init(); }
void pilot_release(CCaDiCaL *p) { ccadical_release(p); }
void pilot_add(CCaDiCaL *p, int lit) { ccadical_add(p, lit); }
void pilot_assume(CCaDiCaL *p, int lit) { ccadical_assume(p, lit); }
void pilot_freeze(CCaDiCaL *p, int lit) { ccadical_freeze(p, lit); }
int pilot_solve(CCaDiCaL *p) { return ccadical_solve(p); }
int pilot_val(CCaDiCaL *p, int lit) { return ccadical_val(p, lit); }
void pilot_set_option(CCaDiCaL *p, const char *name, int val) {
  ccadical_set_option(p, name, val);
}
void pilot_set_terminate(CCaDiCaL *p, void *state, int (*callback)(void *)) {
  ccadical_set_terminate(p, state, callback);
}
}
