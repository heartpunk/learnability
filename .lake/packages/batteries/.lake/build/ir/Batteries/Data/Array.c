// Lean compiler output
// Module: Batteries.Data.Array
// Imports: public import Init public import Batteries.Data.Array.Basic public import Batteries.Data.Array.Init.Lemmas public import Batteries.Data.Array.Lemmas public import Batteries.Data.Array.Match public import Batteries.Data.Array.Merge public import Batteries.Data.Array.Monadic public import Batteries.Data.Array.Pairwise public import Batteries.Data.Array.Scan
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
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_batteries_Batteries_Data_Array_Basic(uint8_t builtin);
lean_object* initialize_batteries_Batteries_Data_Array_Init_Lemmas(uint8_t builtin);
lean_object* initialize_batteries_Batteries_Data_Array_Lemmas(uint8_t builtin);
lean_object* initialize_batteries_Batteries_Data_Array_Match(uint8_t builtin);
lean_object* initialize_batteries_Batteries_Data_Array_Merge(uint8_t builtin);
lean_object* initialize_batteries_Batteries_Data_Array_Monadic(uint8_t builtin);
lean_object* initialize_batteries_Batteries_Data_Array_Pairwise(uint8_t builtin);
lean_object* initialize_batteries_Batteries_Data_Array_Scan(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_batteries_Batteries_Data_Array(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_batteries_Batteries_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_batteries_Batteries_Data_Array_Init_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_batteries_Batteries_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_batteries_Batteries_Data_Array_Match(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_batteries_Batteries_Data_Array_Merge(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_batteries_Batteries_Data_Array_Monadic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_batteries_Batteries_Data_Array_Pairwise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_batteries_Batteries_Data_Array_Scan(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
