// Lean compiler output
// Module: Batteries.Data.FloatArray
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
static lean_object* lp_batteries_FloatArray_map___closed__2;
static lean_object* lp_batteries_FloatArray_map___closed__5;
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_sarray_size(lean_object*);
LEAN_EXPORT lean_object* lp_batteries_FloatArray_mapMUnsafe_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
static lean_object* lp_batteries_FloatArray_map___closed__1;
static lean_object* lp_batteries_FloatArray_map___closed__3;
lean_object* lean_float_array_uset(lean_object*, size_t, double);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* lp_batteries_FloatArray_map___closed__6;
LEAN_EXPORT lean_object* lp_batteries_FloatArray_mapMUnsafe___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_FloatArray_mapMUnsafe_loop___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t);
static lean_object* lp_batteries_FloatArray_map___closed__8;
LEAN_EXPORT lean_object* lp_batteries_FloatArray_mapMUnsafe_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* lp_batteries_FloatArray_map(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_FloatArray_mapMUnsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
static lean_object* lp_batteries_FloatArray_map___closed__4;
LEAN_EXPORT lean_object* lp_batteries_FloatArray_mapMUnsafe_loop___redArg___lam__0(lean_object*, size_t, lean_object*, lean_object*, size_t, double);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* lp_batteries_FloatArray_map___closed__7;
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* lp_batteries_FloatArray_mapMUnsafe(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_FloatArray_mapMUnsafe_loop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* lp_batteries_FloatArray_map___closed__9;
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* lp_batteries_FloatArray_map___closed__0;
LEAN_EXPORT lean_object* lp_batteries_FloatArray_mapMUnsafe_loop___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; double x_9; lean_object* x_10; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_float(x_6);
lean_dec_ref(x_6);
x_10 = lp_batteries_FloatArray_mapMUnsafe_loop___redArg___lam__0(x_1, x_7, x_3, x_4, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* lp_batteries_FloatArray_mapMUnsafe_loop___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; double x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_box_usize(x_4);
x_12 = lean_box_usize(x_5);
lean_inc(x_2);
lean_inc_ref(x_3);
x_13 = lean_alloc_closure((void*)(lp_batteries_FloatArray_mapMUnsafe_loop___redArg___lam__0___boxed), 6, 5);
lean_closure_set(x_13, 0, x_3);
lean_closure_set(x_13, 1, x_11);
lean_closure_set(x_13, 2, x_1);
lean_closure_set(x_13, 3, x_2);
lean_closure_set(x_13, 4, x_12);
x_14 = lean_float_array_uget(x_3, x_4);
lean_dec_ref(x_3);
x_15 = lean_box_float(x_14);
x_16 = lean_apply_1(x_2, x_15);
x_17 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_16, x_13);
return x_17;
}
}
}
LEAN_EXPORT lean_object* lp_batteries_FloatArray_mapMUnsafe_loop___redArg___lam__0(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, size_t x_5, double x_6) {
_start:
{
lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_float_array_uset(x_1, x_2, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_10 = lp_batteries_FloatArray_mapMUnsafe_loop___redArg(x_3, x_4, x_7, x_9, x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* lp_batteries_FloatArray_mapMUnsafe_loop___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = lp_batteries_FloatArray_mapMUnsafe_loop___redArg(x_1, x_2, x_3, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_batteries_FloatArray_mapMUnsafe_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_batteries_FloatArray_mapMUnsafe_loop___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_batteries_FloatArray_mapMUnsafe_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_9 = lp_batteries_FloatArray_mapMUnsafe_loop(x_1, x_2, x_3, x_4, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_batteries_FloatArray_mapMUnsafe___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = 0;
x_5 = lean_sarray_size(x_2);
x_6 = lp_batteries_FloatArray_mapMUnsafe_loop___redArg(x_1, x_3, x_2, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_batteries_FloatArray_mapMUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = 0;
x_6 = lean_sarray_size(x_3);
x_7 = lp_batteries_FloatArray_mapMUnsafe_loop___redArg(x_2, x_4, x_3, x_5, x_6);
return x_7;
}
}
static lean_object* _init_lp_batteries_FloatArray_map___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
return x_1;
}
}
static lean_object* _init_lp_batteries_FloatArray_map___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_lp_batteries_FloatArray_map___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_lp_batteries_FloatArray_map___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
return x_1;
}
}
static lean_object* _init_lp_batteries_FloatArray_map___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_lp_batteries_FloatArray_map___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_lp_batteries_FloatArray_map___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
return x_1;
}
}
static lean_object* _init_lp_batteries_FloatArray_map___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_batteries_FloatArray_map___closed__1;
x_2 = lp_batteries_FloatArray_map___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_batteries_FloatArray_map___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lp_batteries_FloatArray_map___closed__5;
x_2 = lp_batteries_FloatArray_map___closed__4;
x_3 = lp_batteries_FloatArray_map___closed__3;
x_4 = lp_batteries_FloatArray_map___closed__2;
x_5 = lp_batteries_FloatArray_map___closed__7;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_lp_batteries_FloatArray_map___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_batteries_FloatArray_map___closed__6;
x_2 = lp_batteries_FloatArray_map___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_batteries_FloatArray_map(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lp_batteries_FloatArray_map___closed__9;
x_4 = 0;
x_5 = lean_sarray_size(x_1);
x_6 = lp_batteries_FloatArray_mapMUnsafe_loop___redArg(x_3, x_2, x_1, x_4, x_5);
return x_6;
}
}
lean_object* initialize_Init(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_batteries_Batteries_Data_FloatArray(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_batteries_FloatArray_map___closed__0 = _init_lp_batteries_FloatArray_map___closed__0();
lean_mark_persistent(lp_batteries_FloatArray_map___closed__0);
lp_batteries_FloatArray_map___closed__1 = _init_lp_batteries_FloatArray_map___closed__1();
lean_mark_persistent(lp_batteries_FloatArray_map___closed__1);
lp_batteries_FloatArray_map___closed__2 = _init_lp_batteries_FloatArray_map___closed__2();
lean_mark_persistent(lp_batteries_FloatArray_map___closed__2);
lp_batteries_FloatArray_map___closed__3 = _init_lp_batteries_FloatArray_map___closed__3();
lean_mark_persistent(lp_batteries_FloatArray_map___closed__3);
lp_batteries_FloatArray_map___closed__4 = _init_lp_batteries_FloatArray_map___closed__4();
lean_mark_persistent(lp_batteries_FloatArray_map___closed__4);
lp_batteries_FloatArray_map___closed__5 = _init_lp_batteries_FloatArray_map___closed__5();
lean_mark_persistent(lp_batteries_FloatArray_map___closed__5);
lp_batteries_FloatArray_map___closed__6 = _init_lp_batteries_FloatArray_map___closed__6();
lean_mark_persistent(lp_batteries_FloatArray_map___closed__6);
lp_batteries_FloatArray_map___closed__7 = _init_lp_batteries_FloatArray_map___closed__7();
lean_mark_persistent(lp_batteries_FloatArray_map___closed__7);
lp_batteries_FloatArray_map___closed__8 = _init_lp_batteries_FloatArray_map___closed__8();
lean_mark_persistent(lp_batteries_FloatArray_map___closed__8);
lp_batteries_FloatArray_map___closed__9 = _init_lp_batteries_FloatArray_map___closed__9();
lean_mark_persistent(lp_batteries_FloatArray_map___closed__9);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
