// Lean compiler output
// Module: Batteries.Data.Bool
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
LEAN_EXPORT lean_object* lp_batteries_Bool_lt__wfRel;
LEAN_EXPORT lean_object* lp_batteries_Bool_gt__wfRel;
static lean_object* _init_lp_batteries_Bool_lt__wfRel() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_lp_batteries_Bool_gt__wfRel() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_batteries_Batteries_Data_Bool(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_batteries_Bool_lt__wfRel = _init_lp_batteries_Bool_lt__wfRel();
lean_mark_persistent(lp_batteries_Bool_lt__wfRel);
lp_batteries_Bool_gt__wfRel = _init_lp_batteries_Bool_gt__wfRel();
lean_mark_persistent(lp_batteries_Bool_gt__wfRel);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
