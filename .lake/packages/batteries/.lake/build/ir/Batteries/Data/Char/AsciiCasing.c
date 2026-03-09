// Lean compiler output
// Module: Batteries.Data.Char.AsciiCasing
// Imports: public import Init public import Batteries.Data.Char.Basic public import Batteries.Tactic.Basic
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
LEAN_EXPORT lean_object* lp_batteries_Char_cmpCaseInsensitiveAsciiOnly___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Char_beqCaseInsensitiveAsciiOnly___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_batteries_Char_cmpCaseInsensitiveAsciiOnly(uint32_t, uint32_t);
LEAN_EXPORT lean_object* lp_batteries_Char_caseFoldAsciiOnly___boxed(lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
LEAN_EXPORT uint32_t lp_batteries_Char_caseFoldAsciiOnly(uint32_t);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
LEAN_EXPORT lean_object* lp_batteries_Char_beqCaseInsensitiveAsciiOnly_isSetoid;
uint32_t lean_uint32_add(uint32_t, uint32_t);
LEAN_EXPORT uint8_t lp_batteries_Char_beqCaseInsensitiveAsciiOnly(uint32_t, uint32_t);
LEAN_EXPORT uint32_t lp_batteries_Char_caseFoldAsciiOnly(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 65;
x_3 = lean_uint32_dec_le(x_2, x_1);
if (x_3 == 0)
{
return x_1;
}
else
{
uint32_t x_4; uint8_t x_5; 
x_4 = 90;
x_5 = lean_uint32_dec_le(x_1, x_4);
if (x_5 == 0)
{
return x_1;
}
else
{
uint32_t x_6; uint32_t x_7; 
x_6 = 32;
x_7 = lean_uint32_add(x_1, x_6);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* lp_batteries_Char_caseFoldAsciiOnly___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint32_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = lp_batteries_Char_caseFoldAsciiOnly(x_2);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t lp_batteries_Char_beqCaseInsensitiveAsciiOnly(uint32_t x_1, uint32_t x_2) {
_start:
{
uint32_t x_3; uint32_t x_14; uint8_t x_15; 
x_14 = 65;
x_15 = lean_uint32_dec_le(x_14, x_1);
if (x_15 == 0)
{
x_3 = x_1;
goto block_13;
}
else
{
uint32_t x_16; uint8_t x_17; 
x_16 = 90;
x_17 = lean_uint32_dec_le(x_1, x_16);
if (x_17 == 0)
{
x_3 = x_1;
goto block_13;
}
else
{
uint32_t x_18; uint32_t x_19; 
x_18 = 32;
x_19 = lean_uint32_add(x_1, x_18);
x_3 = x_19;
goto block_13;
}
}
block_13:
{
uint32_t x_4; uint8_t x_5; 
x_4 = 65;
x_5 = lean_uint32_dec_le(x_4, x_2);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = lean_uint32_dec_eq(x_3, x_2);
return x_6;
}
else
{
uint32_t x_7; uint8_t x_8; 
x_7 = 90;
x_8 = lean_uint32_dec_le(x_2, x_7);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = lean_uint32_dec_eq(x_3, x_2);
return x_9;
}
else
{
uint32_t x_10; uint32_t x_11; uint8_t x_12; 
x_10 = 32;
x_11 = lean_uint32_add(x_2, x_10);
x_12 = lean_uint32_dec_eq(x_3, x_11);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_batteries_Char_beqCaseInsensitiveAsciiOnly___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lp_batteries_Char_beqCaseInsensitiveAsciiOnly(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_lp_batteries_Char_beqCaseInsensitiveAsciiOnly_isSetoid() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t lp_batteries_Char_cmpCaseInsensitiveAsciiOnly(uint32_t x_1, uint32_t x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint32_t x_11; uint32_t x_19; uint8_t x_20; 
x_19 = 65;
x_20 = lean_uint32_dec_le(x_19, x_1);
if (x_20 == 0)
{
x_11 = x_1;
goto block_18;
}
else
{
uint32_t x_21; uint8_t x_22; 
x_21 = 90;
x_22 = lean_uint32_dec_le(x_1, x_21);
if (x_22 == 0)
{
x_11 = x_1;
goto block_18;
}
else
{
uint32_t x_23; uint32_t x_24; 
x_23 = 32;
x_24 = lean_uint32_add(x_1, x_23);
x_11 = x_24;
goto block_18;
}
}
block_10:
{
uint8_t x_5; 
x_5 = lean_uint32_dec_lt(x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = lean_uint32_dec_eq(x_3, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 2;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
}
block_18:
{
uint32_t x_12; uint8_t x_13; 
x_12 = 65;
x_13 = lean_uint32_dec_le(x_12, x_2);
if (x_13 == 0)
{
x_3 = x_11;
x_4 = x_2;
goto block_10;
}
else
{
uint32_t x_14; uint8_t x_15; 
x_14 = 90;
x_15 = lean_uint32_dec_le(x_2, x_14);
if (x_15 == 0)
{
x_3 = x_11;
x_4 = x_2;
goto block_10;
}
else
{
uint32_t x_16; uint32_t x_17; 
x_16 = 32;
x_17 = lean_uint32_add(x_2, x_16);
x_3 = x_11;
x_4 = x_17;
goto block_10;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_batteries_Char_cmpCaseInsensitiveAsciiOnly___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lp_batteries_Char_cmpCaseInsensitiveAsciiOnly(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_batteries_Batteries_Data_Char_Basic(uint8_t builtin);
lean_object* initialize_batteries_Batteries_Tactic_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_batteries_Batteries_Data_Char_AsciiCasing(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_batteries_Batteries_Data_Char_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_batteries_Batteries_Tactic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_batteries_Char_beqCaseInsensitiveAsciiOnly_isSetoid = _init_lp_batteries_Char_beqCaseInsensitiveAsciiOnly_isSetoid();
lean_mark_persistent(lp_batteries_Char_beqCaseInsensitiveAsciiOnly_isSetoid);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
