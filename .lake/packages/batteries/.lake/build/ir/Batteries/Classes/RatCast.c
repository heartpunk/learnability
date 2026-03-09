// Lean compiler output
// Module: Batteries.Classes.RatCast
// Imports: public import Init
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
static lean_object* lp_batteries_instRatCastRat___closed__0;
LEAN_EXPORT lean_object* lp_batteries_Rat_cast(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_instCoeHTCTRatOfRatCast___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_batteries_instRatCastRat___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_batteries_instRatCastRat;
LEAN_EXPORT lean_object* lp_batteries_instCoeTailRatOfRatCast___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_batteries_instCoeTailRatOfRatCast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_instCoeHTCTRatOfRatCast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Rat_cast___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_instRatCastRat___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_batteries_instRatCastRat___lam__0(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_batteries_instRatCastRat___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_batteries_instRatCastRat___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_lp_batteries_instRatCastRat___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lp_batteries_instRatCastRat___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_lp_batteries_instRatCastRat() {
_start:
{
lean_object* x_1; 
x_1 = lp_batteries_instRatCastRat___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* lp_batteries_Rat_cast___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_batteries_Rat_cast(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_batteries_instCoeTailRatOfRatCast___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(lp_batteries_Rat_cast), 3, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_batteries_instCoeTailRatOfRatCast(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(lp_batteries_Rat_cast), 3, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_batteries_instCoeHTCTRatOfRatCast___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(lp_batteries_Rat_cast), 3, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_batteries_instCoeHTCTRatOfRatCast(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(lp_batteries_Rat_cast), 3, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_batteries_Batteries_Classes_RatCast(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_batteries_instRatCastRat___closed__0 = _init_lp_batteries_instRatCastRat___closed__0();
lean_mark_persistent(lp_batteries_instRatCastRat___closed__0);
lp_batteries_instRatCastRat = _init_lp_batteries_instRatCastRat();
lean_mark_persistent(lp_batteries_instRatCastRat);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
