// Lean compiler output
// Module: Batteries.Data.ByteArray
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
LEAN_EXPORT lean_object* lp_batteries_ByteArray_mapMUnsafe(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_ByteArray_mapMUnsafe_loop___redArg(lean_object*, lean_object*, lean_object*, size_t);
lean_object* lean_mk_empty_byte_array(lean_object*);
LEAN_EXPORT lean_object* lp_batteries_ByteArray_mapMUnsafe_loop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqUInt8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_ByteArray_ofFn___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_ByteArray_ofFn(lean_object*, lean_object*);
lean_object* lean_byte_array_push(lean_object*, uint8_t);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_ByteArray_mapMUnsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Data_ByteArray_0__ByteArray_get_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_ByteArray_mapMUnsafe_loop___redArg___lam__0(lean_object*, size_t, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Data_ByteArray_0__ByteArray_get_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_instDecidableEqImpl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_batteries_ByteArray_instDecidableEq__batteries(lean_object*, lean_object*);
size_t lean_sarray_size(lean_object*);
LEAN_EXPORT lean_object* lp_batteries_ByteArray_mapMUnsafe_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
static lean_object* lp_batteries_ByteArray_map___closed__1;
uint8_t lean_byte_array_uget(lean_object*, size_t);
static lean_object* lp_batteries_ByteArray_map___closed__0;
static lean_object* lp_batteries_ByteArray_map___closed__5;
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Data_ByteArray_0__ByteArray_size_match__1_splitter(lean_object*, lean_object*, lean_object*);
static lean_object* lp_batteries_ByteArray_map___closed__4;
static lean_object* lp_batteries_ByteArray_map___closed__9;
lean_object* lean_byte_array_data(lean_object*);
static lean_object* lp_batteries_ByteArray_map___closed__2;
lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldl_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* lp_batteries_ByteArray_map___closed__3;
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* lp_batteries_ByteArray_map___closed__7;
LEAN_EXPORT lean_object* lp_batteries_ByteArray_mapMUnsafe_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* lp_batteries_ByteArray_map___closed__6;
LEAN_EXPORT lean_object* lp_batteries_ByteArray_instDecidableEq__batteries___boxed(lean_object*, lean_object*);
static lean_object* lp_batteries_ByteArray_map___closed__8;
lean_object* lean_byte_array_uset(lean_object*, size_t, uint8_t);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_ByteArray_ofFn___boxed(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* lp_batteries_ByteArray_mapMUnsafe___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Data_ByteArray_0__ByteArray_size_match__1_splitter___redArg(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_ByteArray_map(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_batteries_ByteArray_instDecidableEq__batteries(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_alloc_closure((void*)(l_instDecidableEqUInt8___boxed), 2, 0);
x_4 = lean_byte_array_data(x_1);
x_5 = lean_byte_array_data(x_2);
x_6 = l_Array_instDecidableEqImpl___redArg(x_3, x_4, x_5);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_batteries_ByteArray_instDecidableEq__batteries___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lp_batteries_ByteArray_instDecidableEq__batteries(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_batteries_ByteArray_ofFn___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_unbox(x_4);
x_6 = lean_byte_array_push(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_batteries_ByteArray_ofFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_alloc_closure((void*)(lp_batteries_ByteArray_ofFn___lam__0), 3, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_mk_empty_byte_array(x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l___private_Init_Data_Fin_Fold_0__Fin_foldl_loop(lean_box(0), x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_batteries_ByteArray_ofFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_batteries_ByteArray_ofFn(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Data_ByteArray_0__ByteArray_size_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_byte_array_data(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Data_ByteArray_0__ByteArray_size_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_batteries___private_Batteries_Data_ByteArray_0__ByteArray_size_match__1_splitter___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Data_ByteArray_0__ByteArray_get_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_byte_array_data(x_1);
x_5 = lean_apply_3(x_3, x_4, x_2, lean_box(0));
return x_5;
}
}
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Data_ByteArray_0__ByteArray_get_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_batteries___private_Batteries_Data_ByteArray_0__ByteArray_get_match__1_splitter___redArg(x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_batteries_ByteArray_mapMUnsafe_loop___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox(x_5);
x_8 = lp_batteries_ByteArray_mapMUnsafe_loop___redArg___lam__0(x_1, x_6, x_3, x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_batteries_ByteArray_mapMUnsafe_loop___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4) {
_start:
{
size_t x_5; uint8_t x_6; 
x_5 = lean_sarray_size(x_3);
x_6 = lean_usize_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_7);
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = lean_apply_2(x_8, lean_box(0), x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_box_usize(x_4);
lean_inc(x_2);
lean_inc_ref(x_3);
x_12 = lean_alloc_closure((void*)(lp_batteries_ByteArray_mapMUnsafe_loop___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_12, 0, x_3);
lean_closure_set(x_12, 1, x_11);
lean_closure_set(x_12, 2, x_1);
lean_closure_set(x_12, 3, x_2);
x_13 = lean_byte_array_uget(x_3, x_4);
lean_dec_ref(x_3);
x_14 = lean_box(x_13);
x_15 = lean_apply_1(x_2, x_14);
x_16 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_15, x_12);
return x_16;
}
}
}
LEAN_EXPORT lean_object* lp_batteries_ByteArray_mapMUnsafe_loop___redArg___lam__0(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_6 = lean_byte_array_uset(x_1, x_2, x_5);
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
x_9 = lp_batteries_ByteArray_mapMUnsafe_loop___redArg(x_3, x_4, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_batteries_ByteArray_mapMUnsafe_loop___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_6 = lp_batteries_ByteArray_mapMUnsafe_loop___redArg(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_batteries_ByteArray_mapMUnsafe_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_batteries_ByteArray_mapMUnsafe_loop___redArg(x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_batteries_ByteArray_mapMUnsafe_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_9 = lp_batteries_ByteArray_mapMUnsafe_loop(x_1, x_2, x_3, x_4, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_batteries_ByteArray_mapMUnsafe___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = 0;
x_5 = lp_batteries_ByteArray_mapMUnsafe_loop___redArg(x_1, x_3, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_batteries_ByteArray_mapMUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = 0;
x_6 = lp_batteries_ByteArray_mapMUnsafe_loop___redArg(x_2, x_4, x_3, x_5);
return x_6;
}
}
static lean_object* _init_lp_batteries_ByteArray_map___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
return x_1;
}
}
static lean_object* _init_lp_batteries_ByteArray_map___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_lp_batteries_ByteArray_map___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_lp_batteries_ByteArray_map___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
return x_1;
}
}
static lean_object* _init_lp_batteries_ByteArray_map___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_lp_batteries_ByteArray_map___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_lp_batteries_ByteArray_map___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
return x_1;
}
}
static lean_object* _init_lp_batteries_ByteArray_map___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_batteries_ByteArray_map___closed__1;
x_2 = lp_batteries_ByteArray_map___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_batteries_ByteArray_map___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lp_batteries_ByteArray_map___closed__5;
x_2 = lp_batteries_ByteArray_map___closed__4;
x_3 = lp_batteries_ByteArray_map___closed__3;
x_4 = lp_batteries_ByteArray_map___closed__2;
x_5 = lp_batteries_ByteArray_map___closed__7;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_lp_batteries_ByteArray_map___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_batteries_ByteArray_map___closed__6;
x_2 = lp_batteries_ByteArray_map___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_batteries_ByteArray_map(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; 
x_3 = lp_batteries_ByteArray_map___closed__9;
x_4 = 0;
x_5 = lp_batteries_ByteArray_mapMUnsafe_loop___redArg(x_3, x_2, x_1, x_4);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_batteries_Batteries_Data_ByteArray(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_batteries_ByteArray_map___closed__0 = _init_lp_batteries_ByteArray_map___closed__0();
lean_mark_persistent(lp_batteries_ByteArray_map___closed__0);
lp_batteries_ByteArray_map___closed__1 = _init_lp_batteries_ByteArray_map___closed__1();
lean_mark_persistent(lp_batteries_ByteArray_map___closed__1);
lp_batteries_ByteArray_map___closed__2 = _init_lp_batteries_ByteArray_map___closed__2();
lean_mark_persistent(lp_batteries_ByteArray_map___closed__2);
lp_batteries_ByteArray_map___closed__3 = _init_lp_batteries_ByteArray_map___closed__3();
lean_mark_persistent(lp_batteries_ByteArray_map___closed__3);
lp_batteries_ByteArray_map___closed__4 = _init_lp_batteries_ByteArray_map___closed__4();
lean_mark_persistent(lp_batteries_ByteArray_map___closed__4);
lp_batteries_ByteArray_map___closed__5 = _init_lp_batteries_ByteArray_map___closed__5();
lean_mark_persistent(lp_batteries_ByteArray_map___closed__5);
lp_batteries_ByteArray_map___closed__6 = _init_lp_batteries_ByteArray_map___closed__6();
lean_mark_persistent(lp_batteries_ByteArray_map___closed__6);
lp_batteries_ByteArray_map___closed__7 = _init_lp_batteries_ByteArray_map___closed__7();
lean_mark_persistent(lp_batteries_ByteArray_map___closed__7);
lp_batteries_ByteArray_map___closed__8 = _init_lp_batteries_ByteArray_map___closed__8();
lean_mark_persistent(lp_batteries_ByteArray_map___closed__8);
lp_batteries_ByteArray_map___closed__9 = _init_lp_batteries_ByteArray_map___closed__9();
lean_mark_persistent(lp_batteries_ByteArray_map___closed__9);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
