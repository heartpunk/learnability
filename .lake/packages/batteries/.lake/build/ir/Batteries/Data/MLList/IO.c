// Lean compiler output
// Module: Batteries.Data.MLList.IO
// Imports: public import Init public import Batteries.Lean.System.IO public import Batteries.Data.MLList.Basic
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
LEAN_EXPORT lean_object* lp_batteries_MLList_ofTaskList___redArg(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_batteries_MLList_ofTaskList___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_batteries_MLList_fix_x3f_x27___at___00MLList_ofTaskList_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* lp_batteries_MLList_ofTaskList___redArg___closed__0;
LEAN_EXPORT lean_object* lp_batteries_MLList_ofTaskList(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_MLList_fix_x3f_x27___at___00MLList_ofTaskList_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_waitAny_x27___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_batteries_MLList_ofTaskList___redArg___lam__0___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_MLList_fix_x3f_x27___at___00MLList_ofTaskList_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_MLList_fix_x3f_x27___at___00MLList_ofTaskList_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_MLList_ofTaskList___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_List_lengthTR___redArg(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_IO_waitAny_x27___redArg(x_1);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* lp_batteries_MLList_ofTaskList___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_batteries_MLList_ofTaskList___redArg___lam__0(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_batteries_MLList_fix_x3f_x27___at___00MLList_ofTaskList_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
lean_inc_ref(x_1);
x_5 = lean_apply_2(x_1, x_2, lean_box(0));
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_dec_ref(x_1);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 1);
x_10 = lp_batteries_MLList_fix_x3f_x27___at___00MLList_ofTaskList_spec__0___redArg(x_1, x_9);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 1, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = lp_batteries_MLList_fix_x3f_x27___at___00MLList_ofTaskList_spec__0___redArg(x_1, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* lp_batteries_MLList_fix_x3f_x27___at___00MLList_ofTaskList_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_batteries_MLList_fix_x3f_x27___at___00MLList_ofTaskList_spec__0___redArg___lam__0(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_batteries_MLList_fix_x3f_x27___at___00MLList_ofTaskList_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(lp_batteries_MLList_fix_x3f_x27___at___00MLList_ofTaskList_spec__0___redArg___lam__0___boxed), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
static lean_object* _init_lp_batteries_MLList_ofTaskList___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lp_batteries_MLList_ofTaskList___redArg___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_batteries_MLList_ofTaskList___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lp_batteries_MLList_ofTaskList___redArg___closed__0;
x_3 = lp_batteries_MLList_fix_x3f_x27___at___00MLList_ofTaskList_spec__0___redArg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_batteries_MLList_ofTaskList(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_batteries_MLList_ofTaskList___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_batteries_MLList_fix_x3f_x27___at___00MLList_ofTaskList_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_batteries_MLList_fix_x3f_x27___at___00MLList_ofTaskList_spec__0___redArg(x_3, x_4);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_batteries_Batteries_Lean_System_IO(uint8_t builtin);
lean_object* initialize_batteries_Batteries_Data_MLList_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_batteries_Batteries_Data_MLList_IO(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_batteries_Batteries_Lean_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_batteries_Batteries_Data_MLList_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_batteries_MLList_ofTaskList___redArg___closed__0 = _init_lp_batteries_MLList_ofTaskList___redArg___closed__0();
lean_mark_persistent(lp_batteries_MLList_ofTaskList___redArg___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
