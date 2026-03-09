// Lean compiler output
// Module: Batteries.Data.DList.Lemmas
// Imports: public import Init public import Batteries.Data.DList.Basic
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
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Data_DList_Lemmas_0__Batteries_DList_cons_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Data_DList_Lemmas_0__Batteries_DList_append_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Data_DList_Lemmas_0__Batteries_DList_append_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Data_DList_Lemmas_0__Batteries_DList_push_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Data_DList_Lemmas_0__Batteries_DList_push_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Data_DList_Lemmas_0__Batteries_DList_cons_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Data_DList_Lemmas_0__Batteries_DList_append_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_4(x_3, x_1, lean_box(0), x_2, lean_box(0));
return x_4;
}
}
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Data_DList_Lemmas_0__Batteries_DList_append_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_4(x_5, x_3, lean_box(0), x_4, lean_box(0));
return x_6;
}
}
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Data_DList_Lemmas_0__Batteries_DList_cons_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_3(x_3, x_1, x_2, lean_box(0));
return x_4;
}
}
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Data_DList_Lemmas_0__Batteries_DList_cons_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_3(x_5, x_3, x_4, lean_box(0));
return x_6;
}
}
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Data_DList_Lemmas_0__Batteries_DList_push_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_3(x_3, x_1, lean_box(0), x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Data_DList_Lemmas_0__Batteries_DList_push_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_3(x_5, x_3, lean_box(0), x_4);
return x_6;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_batteries_Batteries_Data_DList_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_batteries_Batteries_Data_DList_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_batteries_Batteries_Data_DList_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
