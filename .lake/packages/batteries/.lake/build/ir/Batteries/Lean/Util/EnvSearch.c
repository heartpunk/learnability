// Lean compiler output
// Module: Batteries.Lean.Util.EnvSearch
// Imports: public import Init public import Batteries.Tactic.Lint.Misc
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
static lean_object* lp_batteries_Lean_getMatchingConstants___redArg___lam__3___closed__0;
lean_object* l_Lean_PersistentHashMap_foldlMAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Lean_getMatchingConstants___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Environment_constants(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Lean_Util_EnvSearch_0__Lean_getMatchingConstants_check___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_batteries_Lean_getMatchingConstants___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Lean_getMatchingConstants___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Lean_getMatchingConstants___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Lean_Util_EnvSearch_0__Lean_getMatchingConstants_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Lean_getMatchingConstants___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Lean_getMatchingConstants___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Lean_getMatchingConstants(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_batteries_Lean_getMatchingConstants___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Lean_Util_EnvSearch_0__Lean_getMatchingConstants_check___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Lean_Util_EnvSearch_0__Lean_getMatchingConstants_check___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Lean_Util_EnvSearch_0__Lean_getMatchingConstants_check___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Lean_getMatchingConstants___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Lean_Util_EnvSearch_0__Lean_getMatchingConstants_check___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec_ref(x_3);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_apply_2(x_5, lean_box(0), x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_array_push(x_2, x_3);
x_9 = lean_apply_2(x_7, lean_box(0), x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Lean_Util_EnvSearch_0__Lean_getMatchingConstants_check___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
x_6 = lp_batteries___private_Batteries_Lean_Util_EnvSearch_0__Lean_getMatchingConstants_check___redArg___lam__0(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Lean_Util_EnvSearch_0__Lean_getMatchingConstants_check___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
lean_inc_ref(x_4);
x_7 = lean_alloc_closure((void*)(lp_batteries___private_Batteries_Lean_Util_EnvSearch_0__Lean_getMatchingConstants_check___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_3);
lean_closure_set(x_7, 2, x_4);
x_8 = lean_apply_1(x_2, x_4);
x_9 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Lean_Util_EnvSearch_0__Lean_getMatchingConstants_check(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_batteries___private_Batteries_Lean_Util_EnvSearch_0__Lean_getMatchingConstants_check___redArg(x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Lean_Util_EnvSearch_0__Lean_getMatchingConstants_check___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_batteries___private_Batteries_Lean_Util_EnvSearch_0__Lean_getMatchingConstants_check(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_batteries_Lean_getMatchingConstants___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_Lean_Environment_constants(x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_6);
lean_dec_ref(x_5);
lean_inc_ref(x_1);
x_7 = lean_alloc_closure((void*)(lp_batteries___private_Batteries_Lean_Util_EnvSearch_0__Lean_getMatchingConstants_check___boxed), 6, 3);
lean_closure_set(x_7, 0, lean_box(0));
lean_closure_set(x_7, 1, x_1);
lean_closure_set(x_7, 2, x_2);
x_8 = l_Lean_PersistentHashMap_foldlMAux___redArg(x_1, x_7, x_6, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_batteries_Lean_getMatchingConstants___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_alloc_closure((void*)(lp_batteries_Lean_getMatchingConstants___redArg___lam__0), 4, 3);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_3);
lean_closure_set(x_7, 2, x_5);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_batteries_Lean_getMatchingConstants___redArg___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_batteries_Lean_getMatchingConstants___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_lp_batteries_Lean_getMatchingConstants___redArg___lam__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_batteries_Lean_getMatchingConstants___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = l_Lean_Environment_constants(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec_ref(x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc_ref(x_9);
lean_dec_ref(x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lp_batteries_Lean_getMatchingConstants___redArg___lam__3___closed__0;
x_12 = lean_array_get_size(x_9);
x_13 = lean_nat_dec_lt(x_10, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec_ref(x_9);
lean_dec(x_5);
lean_dec_ref(x_4);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec_ref(x_1);
x_15 = lean_apply_2(x_14, lean_box(0), x_11);
x_16 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_15, x_3);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_inc_ref(x_4);
x_17 = lean_alloc_closure((void*)(lp_batteries___private_Batteries_Lean_Util_EnvSearch_0__Lean_getMatchingConstants_check___boxed), 6, 3);
lean_closure_set(x_17, 0, lean_box(0));
lean_closure_set(x_17, 1, x_4);
lean_closure_set(x_17, 2, x_5);
lean_inc_ref(x_4);
x_18 = lean_alloc_closure((void*)(lp_batteries_Lean_getMatchingConstants___redArg___lam__4), 4, 2);
lean_closure_set(x_18, 0, x_4);
lean_closure_set(x_18, 1, x_17);
x_19 = lean_nat_dec_le(x_12, x_12);
if (x_19 == 0)
{
if (x_13 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec_ref(x_18);
lean_dec_ref(x_9);
lean_dec_ref(x_4);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_dec_ref(x_1);
x_21 = lean_apply_2(x_20, lean_box(0), x_11);
x_22 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_21, x_3);
return x_22;
}
else
{
size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_1);
x_23 = 0;
x_24 = lean_usize_of_nat(x_12);
x_25 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_4, x_18, x_9, x_23, x_24, x_11);
x_26 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_25, x_3);
return x_26;
}
}
else
{
size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; 
lean_dec_ref(x_1);
x_27 = 0;
x_28 = lean_usize_of_nat(x_12);
x_29 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_4, x_18, x_9, x_27, x_28, x_11);
x_30 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_29, x_3);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* lp_batteries_Lean_getMatchingConstants___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_6);
lean_inc(x_3);
lean_inc_ref(x_1);
lean_inc_ref(x_2);
x_7 = lean_alloc_closure((void*)(lp_batteries_Lean_getMatchingConstants___redArg___lam__1), 5, 4);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_1);
lean_closure_set(x_7, 2, x_3);
lean_closure_set(x_7, 3, x_6);
if (x_4 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec_ref(x_5);
x_9 = lean_alloc_closure((void*)(lp_batteries_Lean_getMatchingConstants___redArg___lam__2), 2, 1);
lean_closure_set(x_9, 0, x_7);
x_10 = lp_batteries_Lean_getMatchingConstants___redArg___lam__3___closed__0;
x_11 = lean_apply_2(x_8, lean_box(0), x_10);
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_11, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec_ref(x_2);
x_14 = lean_alloc_closure((void*)(lp_batteries_Lean_getMatchingConstants___redArg___lam__2), 2, 1);
lean_closure_set(x_14, 0, x_7);
lean_inc(x_6);
x_15 = lean_alloc_closure((void*)(lp_batteries_Lean_getMatchingConstants___redArg___lam__3), 6, 5);
lean_closure_set(x_15, 0, x_5);
lean_closure_set(x_15, 1, x_6);
lean_closure_set(x_15, 2, x_14);
lean_closure_set(x_15, 3, x_1);
lean_closure_set(x_15, 4, x_3);
x_16 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_13, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* lp_batteries_Lean_getMatchingConstants___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
x_6 = lp_batteries_Lean_getMatchingConstants___redArg(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_batteries_Lean_getMatchingConstants(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_batteries_Lean_getMatchingConstants___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_batteries_Lean_getMatchingConstants___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
x_7 = lp_batteries_Lean_getMatchingConstants(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_batteries_Batteries_Tactic_Lint_Misc(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_batteries_Batteries_Lean_Util_EnvSearch(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_batteries_Batteries_Tactic_Lint_Misc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_batteries_Lean_getMatchingConstants___redArg___lam__3___closed__0 = _init_lp_batteries_Lean_getMatchingConstants___redArg___lam__3___closed__0();
lean_mark_persistent(lp_batteries_Lean_getMatchingConstants___redArg___lam__3___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
