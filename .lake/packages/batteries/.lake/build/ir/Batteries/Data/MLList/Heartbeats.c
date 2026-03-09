// Lean compiler output
// Module: Batteries.Data.MLList.Heartbeats
// Imports: public import Init public import Batteries.Data.MLList.Basic public import Lean.Util.Heartbeats
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
LEAN_EXPORT lean_object* lp_batteries_MLList_whileAtLeastHeartbeatsPercent___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_MLList_whileAtLeastHeartbeatsPercent___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_MLList_whileAtLeastHeartbeatsPercent___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_MLList_whileAtLeastHeartbeatsPercent___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getRemainingHeartbeats___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_MLList_whileAtLeastHeartbeatsPercent___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_MLList_whileAtLeastHeartbeatsPercent___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lp_batteries_MLList_takeUpToFirstM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_MLList_whileAtLeastHeartbeatsPercent___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_MLList_whileAtLeastHeartbeatsPercent___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getMaxHeartbeats___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* lp_batteries_MLList_whileAtLeastHeartbeatsPercent___redArg___lam__5___closed__0;
LEAN_EXPORT lean_object* lp_batteries_MLList_whileAtLeastHeartbeatsPercent___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* lp_batteries_MLList_whileAtLeastHeartbeatsPercent___redArg___lam__3___closed__0;
LEAN_EXPORT lean_object* lp_batteries_MLList_whileAtLeastHeartbeatsPercent___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_MLList_whileAtLeastHeartbeatsPercent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_MLList_whileAtLeastHeartbeatsPercent___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_unsigned_to_nat(100u);
x_6 = lean_nat_mul(x_4, x_5);
x_7 = lean_nat_div(x_6, x_1);
lean_dec(x_6);
x_8 = lean_nat_dec_lt(x_7, x_2);
lean_dec(x_7);
x_9 = lean_box(x_8);
x_10 = lean_apply_2(x_3, lean_box(0), x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* lp_batteries_MLList_whileAtLeastHeartbeatsPercent___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_batteries_MLList_whileAtLeastHeartbeatsPercent___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_batteries_MLList_whileAtLeastHeartbeatsPercent___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_4(x_1, lean_box(0), lean_box(0), x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_batteries_MLList_whileAtLeastHeartbeatsPercent___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_batteries_MLList_whileAtLeastHeartbeatsPercent___redArg___lam__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_batteries_MLList_whileAtLeastHeartbeatsPercent___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_2);
x_8 = lean_alloc_closure((void*)(lp_batteries_MLList_whileAtLeastHeartbeatsPercent___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_1);
lean_closure_set(x_8, 2, x_2);
x_9 = lean_alloc_closure((void*)(lp_batteries_MLList_whileAtLeastHeartbeatsPercent___redArg___lam__1___boxed), 4, 3);
lean_closure_set(x_9, 0, x_3);
lean_closure_set(x_9, 1, x_4);
lean_closure_set(x_9, 2, x_8);
x_10 = lp_batteries_MLList_takeUpToFirstM___redArg(x_5, x_6, x_9);
x_11 = lean_apply_2(x_2, lean_box(0), x_10);
return x_11;
}
}
static lean_object* _init_lp_batteries_MLList_whileAtLeastHeartbeatsPercent___redArg___lam__3___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_getRemainingHeartbeats___boxed), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_batteries_MLList_whileAtLeastHeartbeatsPercent___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lp_batteries_MLList_whileAtLeastHeartbeatsPercent___redArg___lam__3___closed__0;
x_9 = lean_apply_2(x_1, lean_box(0), x_8);
lean_inc(x_9);
lean_inc(x_4);
x_10 = lean_alloc_closure((void*)(lp_batteries_MLList_whileAtLeastHeartbeatsPercent___redArg___lam__2), 7, 6);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_4);
lean_closure_set(x_10, 3, x_9);
lean_closure_set(x_10, 4, x_5);
lean_closure_set(x_10, 5, x_6);
x_11 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* lp_batteries_MLList_whileAtLeastHeartbeatsPercent___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_8 = lean_box(0);
x_9 = lean_apply_2(x_1, lean_box(0), x_8);
x_10 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_9, x_3);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_apply_2(x_1, lean_box(0), x_4);
return x_11;
}
}
}
LEAN_EXPORT lean_object* lp_batteries_MLList_whileAtLeastHeartbeatsPercent___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_batteries_MLList_whileAtLeastHeartbeatsPercent___redArg___lam__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
static lean_object* _init_lp_batteries_MLList_whileAtLeastHeartbeatsPercent___redArg___lam__5___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_getMaxHeartbeats___boxed), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_batteries_MLList_whileAtLeastHeartbeatsPercent___redArg___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lp_batteries_MLList_whileAtLeastHeartbeatsPercent___redArg___lam__5___closed__0;
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
x_7 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_6, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_batteries_MLList_whileAtLeastHeartbeatsPercent___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_6);
lean_inc(x_7);
lean_inc(x_2);
x_8 = lean_alloc_closure((void*)(lp_batteries_MLList_whileAtLeastHeartbeatsPercent___redArg___lam__3), 7, 6);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_4);
lean_closure_set(x_8, 2, x_7);
lean_closure_set(x_8, 3, x_6);
lean_closure_set(x_8, 4, x_1);
lean_closure_set(x_8, 5, x_3);
lean_inc(x_6);
x_9 = lean_alloc_closure((void*)(lp_batteries_MLList_whileAtLeastHeartbeatsPercent___redArg___lam__4___boxed), 5, 4);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_6);
lean_closure_set(x_9, 2, x_8);
lean_closure_set(x_9, 3, x_3);
x_10 = lean_alloc_closure((void*)(lp_batteries_MLList_whileAtLeastHeartbeatsPercent___redArg___lam__5), 4, 3);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_6);
lean_closure_set(x_10, 2, x_9);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* lp_batteries_MLList_whileAtLeastHeartbeatsPercent(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_batteries_MLList_whileAtLeastHeartbeatsPercent___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_batteries_Batteries_Data_MLList_Basic(uint8_t builtin);
lean_object* initialize_Lean_Util_Heartbeats(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_batteries_Batteries_Data_MLList_Heartbeats(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_batteries_Batteries_Data_MLList_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Heartbeats(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_batteries_MLList_whileAtLeastHeartbeatsPercent___redArg___lam__3___closed__0 = _init_lp_batteries_MLList_whileAtLeastHeartbeatsPercent___redArg___lam__3___closed__0();
lean_mark_persistent(lp_batteries_MLList_whileAtLeastHeartbeatsPercent___redArg___lam__3___closed__0);
lp_batteries_MLList_whileAtLeastHeartbeatsPercent___redArg___lam__5___closed__0 = _init_lp_batteries_MLList_whileAtLeastHeartbeatsPercent___redArg___lam__5___closed__0();
lean_mark_persistent(lp_batteries_MLList_whileAtLeastHeartbeatsPercent___redArg___lam__5___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
