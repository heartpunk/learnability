// Lean compiler output
// Module: Batteries.Data.NameSet
// Imports: public import Init public import Lean.Data.NameMap.Basic
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
LEAN_EXPORT lean_object* lp_batteries_Lean_NameSet_instInter__batteries___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* lp_batteries_Lean_NameSet_instSDiff__batteries___lam__1___closed__1;
LEAN_EXPORT lean_object* lp_batteries_Lean_NameSet_instUnion__batteries___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Lean_NameSet_instSDiff__batteries___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_quickCmp___boxed(lean_object*, lean_object*);
static lean_object* lp_batteries_Lean_NameSet_instUnion__batteries___closed__1;
LEAN_EXPORT lean_object* lp_batteries_Lean_NameSet_instUnion__batteries___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Lean_NameSet_instSingletonName__batteries;
LEAN_EXPORT lean_object* lp_batteries_Lean_NameSet_instInter__batteries___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Lean_NameSet_instInter__batteries___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
static lean_object* lp_batteries_Lean_NameSet_instSDiff__batteries___lam__1___closed__0;
LEAN_EXPORT lean_object* lp_batteries_Lean_NameSet_instSDiff__batteries___lam__1(lean_object*, lean_object*);
static lean_object* lp_batteries_Lean_NameSet_instSingletonName__batteries___closed__0;
extern lean_object* l_Lean_NameSet_empty;
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Lean_NameSet_instUnion__batteries;
LEAN_EXPORT lean_object* lp_batteries_Lean_NameSet_instInter__batteries;
static lean_object* lp_batteries_Lean_NameSet_instUnion__batteries___closed__0;
lean_object* l_Std_DTreeMap_Internal_Impl_erase___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Lean_NameSet_instSingletonName__batteries___lam__0(lean_object*);
static lean_object* lp_batteries_Lean_NameSet_instInter__batteries___closed__0;
lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* lp_batteries_Lean_NameSet_instSDiff__batteries___closed__0;
LEAN_EXPORT lean_object* lp_batteries_Lean_NameSet_instSDiff__batteries;
LEAN_EXPORT lean_object* lp_batteries_Lean_NameSet_instSingletonName__batteries___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_NameSet_empty;
x_3 = l_Lean_NameSet_insert(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_batteries_Lean_NameSet_instSingletonName__batteries___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lp_batteries_Lean_NameSet_instSingletonName__batteries___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_lp_batteries_Lean_NameSet_instSingletonName__batteries() {
_start:
{
lean_object* x_1; 
x_1 = lp_batteries_Lean_NameSet_instSingletonName__batteries___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* lp_batteries_Lean_NameSet_instUnion__batteries___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_NameSet_insert(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_batteries_Lean_NameSet_instUnion__batteries___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_foldl___redArg(x_1, x_3, x_2);
return x_4;
}
}
static lean_object* _init_lp_batteries_Lean_NameSet_instUnion__batteries___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lp_batteries_Lean_NameSet_instUnion__batteries___lam__0), 3, 0);
return x_1;
}
}
static lean_object* _init_lp_batteries_Lean_NameSet_instUnion__batteries___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lp_batteries_Lean_NameSet_instUnion__batteries___closed__0;
x_2 = lean_alloc_closure((void*)(lp_batteries_Lean_NameSet_instUnion__batteries___lam__1), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_lp_batteries_Lean_NameSet_instUnion__batteries() {
_start:
{
lean_object* x_1; 
x_1 = lp_batteries_Lean_NameSet_instUnion__batteries___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* lp_batteries_Lean_NameSet_instInter__batteries___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_NameSet_contains(x_1, x_3);
if (x_5 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
lean_object* x_6; 
x_6 = l_Lean_NameSet_insert(x_2, x_3);
return x_6;
}
}
}
LEAN_EXPORT lean_object* lp_batteries_Lean_NameSet_instInter__batteries___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_batteries_Lean_NameSet_instInter__batteries___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_batteries_Lean_NameSet_instInter__batteries___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(lp_batteries_Lean_NameSet_instInter__batteries___lam__0___boxed), 4, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lean_NameSet_empty;
x_5 = l_Std_DTreeMap_Internal_Impl_foldl___redArg(x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_lp_batteries_Lean_NameSet_instInter__batteries___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lp_batteries_Lean_NameSet_instInter__batteries___lam__1), 2, 0);
return x_1;
}
}
static lean_object* _init_lp_batteries_Lean_NameSet_instInter__batteries() {
_start:
{
lean_object* x_1; 
x_1 = lp_batteries_Lean_NameSet_instInter__batteries___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* lp_batteries_Lean_NameSet_instSDiff__batteries___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_erase___redArg(x_1, x_3, x_2);
return x_5;
}
}
static lean_object* _init_lp_batteries_Lean_NameSet_instSDiff__batteries___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_quickCmp___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_lp_batteries_Lean_NameSet_instSDiff__batteries___lam__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lp_batteries_Lean_NameSet_instSDiff__batteries___lam__1___closed__0;
x_2 = lean_alloc_closure((void*)(lp_batteries_Lean_NameSet_instSDiff__batteries___lam__0), 4, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_batteries_Lean_NameSet_instSDiff__batteries___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lp_batteries_Lean_NameSet_instSDiff__batteries___lam__1___closed__1;
x_4 = l_Std_DTreeMap_Internal_Impl_foldl___redArg(x_3, x_1, x_2);
return x_4;
}
}
static lean_object* _init_lp_batteries_Lean_NameSet_instSDiff__batteries___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lp_batteries_Lean_NameSet_instSDiff__batteries___lam__1), 2, 0);
return x_1;
}
}
static lean_object* _init_lp_batteries_Lean_NameSet_instSDiff__batteries() {
_start:
{
lean_object* x_1; 
x_1 = lp_batteries_Lean_NameSet_instSDiff__batteries___closed__0;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Lean_Data_NameMap_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_batteries_Batteries_Data_NameSet(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_NameMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_batteries_Lean_NameSet_instSingletonName__batteries___closed__0 = _init_lp_batteries_Lean_NameSet_instSingletonName__batteries___closed__0();
lean_mark_persistent(lp_batteries_Lean_NameSet_instSingletonName__batteries___closed__0);
lp_batteries_Lean_NameSet_instSingletonName__batteries = _init_lp_batteries_Lean_NameSet_instSingletonName__batteries();
lean_mark_persistent(lp_batteries_Lean_NameSet_instSingletonName__batteries);
lp_batteries_Lean_NameSet_instUnion__batteries___closed__0 = _init_lp_batteries_Lean_NameSet_instUnion__batteries___closed__0();
lean_mark_persistent(lp_batteries_Lean_NameSet_instUnion__batteries___closed__0);
lp_batteries_Lean_NameSet_instUnion__batteries___closed__1 = _init_lp_batteries_Lean_NameSet_instUnion__batteries___closed__1();
lean_mark_persistent(lp_batteries_Lean_NameSet_instUnion__batteries___closed__1);
lp_batteries_Lean_NameSet_instUnion__batteries = _init_lp_batteries_Lean_NameSet_instUnion__batteries();
lean_mark_persistent(lp_batteries_Lean_NameSet_instUnion__batteries);
lp_batteries_Lean_NameSet_instInter__batteries___closed__0 = _init_lp_batteries_Lean_NameSet_instInter__batteries___closed__0();
lean_mark_persistent(lp_batteries_Lean_NameSet_instInter__batteries___closed__0);
lp_batteries_Lean_NameSet_instInter__batteries = _init_lp_batteries_Lean_NameSet_instInter__batteries();
lean_mark_persistent(lp_batteries_Lean_NameSet_instInter__batteries);
lp_batteries_Lean_NameSet_instSDiff__batteries___lam__1___closed__0 = _init_lp_batteries_Lean_NameSet_instSDiff__batteries___lam__1___closed__0();
lean_mark_persistent(lp_batteries_Lean_NameSet_instSDiff__batteries___lam__1___closed__0);
lp_batteries_Lean_NameSet_instSDiff__batteries___lam__1___closed__1 = _init_lp_batteries_Lean_NameSet_instSDiff__batteries___lam__1___closed__1();
lean_mark_persistent(lp_batteries_Lean_NameSet_instSDiff__batteries___lam__1___closed__1);
lp_batteries_Lean_NameSet_instSDiff__batteries___closed__0 = _init_lp_batteries_Lean_NameSet_instSDiff__batteries___closed__0();
lean_mark_persistent(lp_batteries_Lean_NameSet_instSDiff__batteries___closed__0);
lp_batteries_Lean_NameSet_instSDiff__batteries = _init_lp_batteries_Lean_NameSet_instSDiff__batteries();
lean_mark_persistent(lp_batteries_Lean_NameSet_instSDiff__batteries);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
