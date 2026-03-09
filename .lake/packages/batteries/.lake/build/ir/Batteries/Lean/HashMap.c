// Lean compiler output
// Module: Batteries.Lean.HashMap
// Imports: public import Init public import Std.Data.HashMap.Basic
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
static lean_object* lp_batteries_Std_HashMap_mergeWith___redArg___closed__1;
LEAN_EXPORT lean_object* lp_batteries_Std_HashMap_mergeWith___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Std_HashMap_mergeWithM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Std_HashMap_mergeWithM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* lp_batteries_Std_HashMap_mergeWith___redArg___closed__9;
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* lp_batteries_Std_HashMap_mergeWith___redArg___closed__5;
static lean_object* lp_batteries_Std_HashMap_mergeWith___redArg___closed__6;
LEAN_EXPORT lean_object* lp_batteries_Std_HashMap_mergeWithM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* lp_batteries_Std_HashMap_mergeWith___redArg___closed__2;
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* lp_batteries_Std_HashMap_mergeWith___redArg___closed__3;
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Std_HashMap_mergeWithM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* lp_batteries_Std_HashMap_mergeWith___redArg___closed__7;
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Std_HashMap_mergeWith___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Std_HashMap_mergeWith___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* lp_batteries_Std_HashMap_mergeWith___redArg___closed__8;
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Std_HashMap_mergeWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* lp_batteries_Std_HashMap_mergeWith___redArg___closed__4;
static lean_object* lp_batteries_Std_HashMap_mergeWith___redArg___closed__0;
LEAN_EXPORT lean_object* lp_batteries_Std_HashMap_mergeWithM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Std_HashMap_mergeWithM___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(x_1, x_2, x_3, x_4, x_6);
x_8 = lean_apply_2(x_5, lean_box(0), x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_batteries_Std_HashMap_mergeWithM___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_9 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(x_1, x_2, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
x_10 = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(x_1, x_2, x_6, x_7, x_8);
x_11 = lean_apply_2(x_3, lean_box(0), x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec_ref(x_9);
lean_inc(x_7);
x_13 = lean_alloc_closure((void*)(lp_batteries_Std_HashMap_mergeWithM___redArg___lam__0), 6, 5);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_6);
lean_closure_set(x_13, 3, x_7);
lean_closure_set(x_13, 4, x_3);
x_14 = lean_apply_3(x_4, x_7, x_12, x_8);
x_15 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_14, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* lp_batteries_Std_HashMap_mergeWithM___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_batteries_Std_HashMap_mergeWithM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
x_9 = lean_ctor_get(x_7, 1);
x_10 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_10);
lean_dec_ref(x_6);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_get_size(x_10);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec_ref(x_10);
lean_inc(x_9);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_14 = lean_apply_2(x_9, lean_box(0), x_5);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_inc(x_8);
lean_inc(x_9);
x_15 = lean_alloc_closure((void*)(lp_batteries_Std_HashMap_mergeWithM___redArg___lam__1), 8, 5);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_9);
lean_closure_set(x_15, 3, x_4);
lean_closure_set(x_15, 4, x_8);
lean_inc_ref(x_3);
x_16 = lean_alloc_closure((void*)(lp_batteries_Std_HashMap_mergeWithM___redArg___lam__2), 4, 2);
lean_closure_set(x_16, 0, x_3);
lean_closure_set(x_16, 1, x_15);
x_17 = lean_nat_dec_le(x_12, x_12);
if (x_17 == 0)
{
if (x_13 == 0)
{
lean_object* x_18; 
lean_dec_ref(x_16);
lean_dec_ref(x_10);
lean_inc(x_9);
lean_dec_ref(x_3);
x_18 = lean_apply_2(x_9, lean_box(0), x_5);
return x_18;
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = 0;
x_20 = lean_usize_of_nat(x_12);
x_21 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_3, x_16, x_10, x_19, x_20, x_5);
return x_21;
}
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; 
x_22 = 0;
x_23 = lean_usize_of_nat(x_12);
x_24 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_3, x_16, x_10, x_22, x_23, x_5);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* lp_batteries_Std_HashMap_mergeWithM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lp_batteries_Std_HashMap_mergeWithM___redArg(x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* lp_batteries_Std_HashMap_mergeWith___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_7 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(x_1, x_2, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_3);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(x_1, x_2, x_4, x_5, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec_ref(x_7);
lean_inc(x_5);
x_10 = lean_apply_3(x_3, x_5, x_9, x_6);
x_11 = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(x_1, x_2, x_4, x_5, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* lp_batteries_Std_HashMap_mergeWith___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_lp_batteries_Std_HashMap_mergeWith___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
return x_1;
}
}
static lean_object* _init_lp_batteries_Std_HashMap_mergeWith___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_lp_batteries_Std_HashMap_mergeWith___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_lp_batteries_Std_HashMap_mergeWith___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
return x_1;
}
}
static lean_object* _init_lp_batteries_Std_HashMap_mergeWith___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_lp_batteries_Std_HashMap_mergeWith___redArg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_lp_batteries_Std_HashMap_mergeWith___redArg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
return x_1;
}
}
static lean_object* _init_lp_batteries_Std_HashMap_mergeWith___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_batteries_Std_HashMap_mergeWith___redArg___closed__1;
x_2 = lp_batteries_Std_HashMap_mergeWith___redArg___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_batteries_Std_HashMap_mergeWith___redArg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lp_batteries_Std_HashMap_mergeWith___redArg___closed__5;
x_2 = lp_batteries_Std_HashMap_mergeWith___redArg___closed__4;
x_3 = lp_batteries_Std_HashMap_mergeWith___redArg___closed__3;
x_4 = lp_batteries_Std_HashMap_mergeWith___redArg___closed__2;
x_5 = lp_batteries_Std_HashMap_mergeWith___redArg___closed__7;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_lp_batteries_Std_HashMap_mergeWith___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_batteries_Std_HashMap_mergeWith___redArg___closed__6;
x_2 = lp_batteries_Std_HashMap_mergeWith___redArg___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_batteries_Std_HashMap_mergeWith___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lp_batteries_Std_HashMap_mergeWith___redArg___closed__9;
x_7 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_7);
lean_dec_ref(x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_get_size(x_7);
x_10 = lean_nat_dec_lt(x_8, x_9);
if (x_10 == 0)
{
lean_dec_ref(x_7);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_alloc_closure((void*)(lp_batteries_Std_HashMap_mergeWith___redArg___lam__0), 6, 3);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_3);
x_12 = lean_alloc_closure((void*)(lp_batteries_Std_HashMap_mergeWith___redArg___lam__1), 4, 2);
lean_closure_set(x_12, 0, x_6);
lean_closure_set(x_12, 1, x_11);
x_13 = lean_nat_dec_le(x_9, x_9);
if (x_13 == 0)
{
if (x_10 == 0)
{
lean_dec_ref(x_12);
lean_dec_ref(x_7);
return x_4;
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = 0;
x_15 = lean_usize_of_nat(x_9);
x_16 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_6, x_12, x_7, x_14, x_15, x_4);
return x_16;
}
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_9);
x_19 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_6, x_12, x_7, x_17, x_18, x_4);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* lp_batteries_Std_HashMap_mergeWith(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lp_batteries_Std_HashMap_mergeWith___redArg___closed__9;
x_9 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_9);
lean_dec_ref(x_7);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_get_size(x_9);
x_12 = lean_nat_dec_lt(x_10, x_11);
if (x_12 == 0)
{
lean_dec_ref(x_9);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_6;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_alloc_closure((void*)(lp_batteries_Std_HashMap_mergeWith___redArg___lam__0), 6, 3);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_3);
lean_closure_set(x_13, 2, x_5);
x_14 = lean_alloc_closure((void*)(lp_batteries_Std_HashMap_mergeWith___redArg___lam__1), 4, 2);
lean_closure_set(x_14, 0, x_8);
lean_closure_set(x_14, 1, x_13);
x_15 = lean_nat_dec_le(x_11, x_11);
if (x_15 == 0)
{
if (x_12 == 0)
{
lean_dec_ref(x_14);
lean_dec_ref(x_9);
return x_6;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_11);
x_18 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_8, x_14, x_9, x_16, x_17, x_6);
return x_18;
}
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = 0;
x_20 = lean_usize_of_nat(x_11);
x_21 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_8, x_14, x_9, x_19, x_20, x_6);
return x_21;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Std_Data_HashMap_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_batteries_Batteries_Lean_HashMap(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_batteries_Std_HashMap_mergeWith___redArg___closed__0 = _init_lp_batteries_Std_HashMap_mergeWith___redArg___closed__0();
lean_mark_persistent(lp_batteries_Std_HashMap_mergeWith___redArg___closed__0);
lp_batteries_Std_HashMap_mergeWith___redArg___closed__1 = _init_lp_batteries_Std_HashMap_mergeWith___redArg___closed__1();
lean_mark_persistent(lp_batteries_Std_HashMap_mergeWith___redArg___closed__1);
lp_batteries_Std_HashMap_mergeWith___redArg___closed__2 = _init_lp_batteries_Std_HashMap_mergeWith___redArg___closed__2();
lean_mark_persistent(lp_batteries_Std_HashMap_mergeWith___redArg___closed__2);
lp_batteries_Std_HashMap_mergeWith___redArg___closed__3 = _init_lp_batteries_Std_HashMap_mergeWith___redArg___closed__3();
lean_mark_persistent(lp_batteries_Std_HashMap_mergeWith___redArg___closed__3);
lp_batteries_Std_HashMap_mergeWith___redArg___closed__4 = _init_lp_batteries_Std_HashMap_mergeWith___redArg___closed__4();
lean_mark_persistent(lp_batteries_Std_HashMap_mergeWith___redArg___closed__4);
lp_batteries_Std_HashMap_mergeWith___redArg___closed__5 = _init_lp_batteries_Std_HashMap_mergeWith___redArg___closed__5();
lean_mark_persistent(lp_batteries_Std_HashMap_mergeWith___redArg___closed__5);
lp_batteries_Std_HashMap_mergeWith___redArg___closed__6 = _init_lp_batteries_Std_HashMap_mergeWith___redArg___closed__6();
lean_mark_persistent(lp_batteries_Std_HashMap_mergeWith___redArg___closed__6);
lp_batteries_Std_HashMap_mergeWith___redArg___closed__7 = _init_lp_batteries_Std_HashMap_mergeWith___redArg___closed__7();
lean_mark_persistent(lp_batteries_Std_HashMap_mergeWith___redArg___closed__7);
lp_batteries_Std_HashMap_mergeWith___redArg___closed__8 = _init_lp_batteries_Std_HashMap_mergeWith___redArg___closed__8();
lean_mark_persistent(lp_batteries_Std_HashMap_mergeWith___redArg___closed__8);
lp_batteries_Std_HashMap_mergeWith___redArg___closed__9 = _init_lp_batteries_Std_HashMap_mergeWith___redArg___closed__9();
lean_mark_persistent(lp_batteries_Std_HashMap_mergeWith___redArg___closed__9);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
