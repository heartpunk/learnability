// Lean compiler output
// Module: Batteries.Data.BitVec.Basic
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
LEAN_EXPORT lean_object* lp_batteries_BitVec_ofFnLE___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_BitVec_ofFnBE___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_BitVec_ofFnLEAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_BitVec_ofFnLEAux___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_BitVec_ofFnBE___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_shiftConcat(lean_object*, lean_object*, uint8_t);
lean_object* l_Fin_foldr_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_BitVec_ofFnLE___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_BitVec_ofFnLE(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_BitVec_ofFnLEAux___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_BitVec_ofFnBE(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_BitVec_ofFnLEAux___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_apply_1(x_1, x_3);
x_6 = lean_unbox(x_5);
x_7 = l_BitVec_shiftConcat(x_2, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_batteries_BitVec_ofFnLEAux___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_batteries_BitVec_ofFnLEAux___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_batteries_BitVec_ofFnLEAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_2);
x_4 = lean_alloc_closure((void*)(lp_batteries_BitVec_ofFnLEAux___lam__0___boxed), 4, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_BitVec_ofNat(x_2, x_5);
lean_dec(x_2);
x_7 = l_Fin_foldr_loop___redArg(x_4, x_1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_batteries_BitVec_ofFnLE___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_apply_1(x_1, x_3);
x_6 = lean_unbox(x_5);
x_7 = l_BitVec_shiftConcat(x_2, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_batteries_BitVec_ofFnLE___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_batteries_BitVec_ofFnLE___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_batteries_BitVec_ofFnLE(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(lp_batteries_BitVec_ofFnLE___lam__0___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_BitVec_ofNat(x_1, x_4);
x_6 = l_Fin_foldr_loop___redArg(x_3, x_1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_batteries_BitVec_ofFnBE___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_3, x_5);
x_7 = lean_nat_sub(x_1, x_6);
lean_dec(x_6);
x_8 = lean_apply_1(x_2, x_7);
x_9 = lean_unbox(x_8);
x_10 = l_BitVec_shiftConcat(x_1, x_4, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* lp_batteries_BitVec_ofFnBE___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_batteries_BitVec_ofFnBE___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_batteries_BitVec_ofFnBE(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(lp_batteries_BitVec_ofFnBE___lam__0___boxed), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_BitVec_ofNat(x_1, x_4);
x_6 = l_Fin_foldr_loop___redArg(x_3, x_1, x_5);
return x_6;
}
}
lean_object* initialize_Init(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_batteries_Batteries_Data_BitVec_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
