// Lean compiler output
// Module: Batteries.Data.DList.Basic
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
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_empty(lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_toList(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_ofList(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_empty___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_push(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_cons___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_instEmptyCollection(lean_object*);
static lean_object* lp_batteries_Batteries_DList_empty___closed__0;
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_ofThunk___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_push___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_empty___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_ofThunk(lean_object*, lean_object*);
lean_object* lean_thunk_get_own(lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_join___redArg(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_cons(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_instAppend(lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_singleton___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_ofList___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Data_DList_Basic_0__Batteries_DList_toList_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_ofThunk___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_instInhabited(lean_object*);
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Data_DList_Basic_0__Batteries_DList_toList_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_join(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_ofList___redArg(lean_object*);
static lean_object* lp_batteries_Batteries_DList_instAppend___closed__0;
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_append___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_cons___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_ofThunk___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_singleton___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_singleton(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_append(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_ofList___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_appendTR___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_ofList___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(lp_batteries_Batteries_DList_ofList___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_ofList(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(lp_batteries_Batteries_DList_ofList___redArg___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_empty___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_empty___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_batteries_Batteries_DList_empty___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_lp_batteries_Batteries_DList_empty___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lp_batteries_Batteries_DList_empty___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_empty(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_batteries_Batteries_DList_empty___closed__0;
return x_2;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_instEmptyCollection(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_batteries_Batteries_DList_empty___closed__0;
return x_2;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_instInhabited(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_batteries_Batteries_DList_empty___closed__0;
return x_2;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_toList___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_toList(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_batteries_Batteries_DList_toList___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Data_DList_Basic_0__Batteries_DList_toList_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_2(x_2, x_1, lean_box(0));
return x_3;
}
}
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Data_DList_Basic_0__Batteries_DList_toList_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_2(x_4, x_3, lean_box(0));
return x_5;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_singleton___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_singleton___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(lp_batteries_Batteries_DList_singleton___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_singleton(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(lp_batteries_Batteries_DList_singleton___redArg___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_cons___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_cons___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(lp_batteries_Batteries_DList_cons___redArg___lam__0), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_cons(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(lp_batteries_Batteries_DList_cons___redArg___lam__0), 3, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_append___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_append___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(lp_batteries_Batteries_DList_append___redArg___lam__0), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_append(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(lp_batteries_Batteries_DList_append___redArg___lam__0), 3, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_push___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_push___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(lp_batteries_Batteries_DList_push___redArg___lam__0), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_push(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(lp_batteries_Batteries_DList_push___redArg___lam__0), 3, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
return x_4;
}
}
static lean_object* _init_lp_batteries_Batteries_DList_instAppend___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lp_batteries_Batteries_DList_append), 3, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_instAppend(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_batteries_Batteries_DList_instAppend___closed__0;
return x_2;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_ofThunk___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_thunk_get_own(x_1);
x_4 = l_List_appendTR___redArg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_ofThunk___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_batteries_Batteries_DList_ofThunk___redArg___lam__0(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_ofThunk___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(lp_batteries_Batteries_DList_ofThunk___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_ofThunk(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(lp_batteries_Batteries_DList_ofThunk___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_join___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lp_batteries_Batteries_DList_empty___closed__0;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lp_batteries_Batteries_DList_join___redArg(x_4);
x_6 = lean_alloc_closure((void*)(lp_batteries_Batteries_DList_append___redArg___lam__0), 3, 2);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_3);
return x_6;
}
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_DList_join(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_batteries_Batteries_DList_join___redArg(x_2);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_batteries_Batteries_Data_DList_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_batteries_Batteries_DList_empty___closed__0 = _init_lp_batteries_Batteries_DList_empty___closed__0();
lean_mark_persistent(lp_batteries_Batteries_DList_empty___closed__0);
lp_batteries_Batteries_DList_instAppend___closed__0 = _init_lp_batteries_Batteries_DList_instAppend___closed__0();
lean_mark_persistent(lp_batteries_Batteries_DList_instAppend___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
