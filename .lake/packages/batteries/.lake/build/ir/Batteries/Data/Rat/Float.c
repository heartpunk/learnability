// Lean compiler output
// Module: Batteries.Data.Rat.Float
// Imports: public import Init public import Batteries.Lean.Float
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
LEAN_EXPORT lean_object* lp_batteries_Float_toRat0(double);
double lp_batteries_Int_divFloat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Float_toRat0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Float_toRat_x3f___boxed(lean_object*);
lean_object* l_Int_sign(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Nat_cast___at___00Float_toRat0_spec__0(lean_object*);
LEAN_EXPORT double lp_batteries_Rat_toFloat(lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Rat_instCoeFloat__batteries;
static lean_object* lp_batteries_Float_toRat0___closed__0;
lean_object* l_mkRat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Rat_toFloat___boxed(lean_object*);
static lean_object* lp_batteries_Rat_instCoeFloat__batteries___closed__0;
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Float_toRat_x3f(double);
LEAN_EXPORT lean_object* lp_batteries_Nat_cast___at___00Rat_toFloat_spec__0(lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lp_batteries_Float_toRatParts(double);
LEAN_EXPORT lean_object* lp_batteries_Nat_cast___at___00Rat_toFloat_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT double lp_batteries_Rat_toFloat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; double x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_nat_to_int(x_3);
x_5 = lp_batteries_Int_divFloat(x_2, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_batteries_Rat_toFloat___boxed(lean_object* x_1) {
_start:
{
double x_2; lean_object* x_3; 
x_2 = lp_batteries_Rat_toFloat(x_1);
x_3 = lean_box_float(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_batteries_Float_toRat_x3f(double x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_batteries_Float_toRatParts(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Int_sign(x_6);
x_9 = lean_nat_abs(x_6);
lean_dec(x_6);
x_10 = l_Int_toNat(x_7);
x_11 = lean_nat_shiftl(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
x_12 = lean_nat_to_int(x_11);
x_13 = lean_int_mul(x_8, x_12);
lean_dec(x_12);
lean_dec(x_8);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_int_neg(x_7);
lean_dec(x_7);
x_16 = l_Int_toNat(x_15);
lean_dec(x_15);
x_17 = lean_nat_shiftl(x_14, x_16);
lean_dec(x_16);
x_18 = l_mkRat(x_13, x_17);
lean_ctor_set(x_2, 0, x_18);
return x_2;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
lean_dec(x_2);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Int_sign(x_20);
x_23 = lean_nat_abs(x_20);
lean_dec(x_20);
x_24 = l_Int_toNat(x_21);
x_25 = lean_nat_shiftl(x_23, x_24);
lean_dec(x_24);
lean_dec(x_23);
x_26 = lean_nat_to_int(x_25);
x_27 = lean_int_mul(x_22, x_26);
lean_dec(x_26);
lean_dec(x_22);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_int_neg(x_21);
lean_dec(x_21);
x_30 = l_Int_toNat(x_29);
lean_dec(x_29);
x_31 = lean_nat_shiftl(x_28, x_30);
lean_dec(x_30);
x_32 = l_mkRat(x_27, x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* lp_batteries_Float_toRat_x3f___boxed(lean_object* x_1) {
_start:
{
double x_2; lean_object* x_3; 
x_2 = lean_unbox_float(x_1);
lean_dec_ref(x_1);
x_3 = lp_batteries_Float_toRat_x3f(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_batteries_Nat_cast___at___00Float_toRat0_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_nat_to_int(x_1);
x_3 = l_Rat_ofInt(x_2);
return x_3;
}
}
static lean_object* _init_lp_batteries_Float_toRat0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lp_batteries_Nat_cast___at___00Float_toRat0_spec__0(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_batteries_Float_toRat0(double x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_batteries_Float_toRat_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lp_batteries_Float_toRat0___closed__0;
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
return x_4;
}
}
}
LEAN_EXPORT lean_object* lp_batteries_Float_toRat0___boxed(lean_object* x_1) {
_start:
{
double x_2; lean_object* x_3; 
x_2 = lean_unbox_float(x_1);
lean_dec_ref(x_1);
x_3 = lp_batteries_Float_toRat0(x_2);
return x_3;
}
}
static lean_object* _init_lp_batteries_Rat_instCoeFloat__batteries___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lp_batteries_Rat_toFloat___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_lp_batteries_Rat_instCoeFloat__batteries() {
_start:
{
lean_object* x_1; 
x_1 = lp_batteries_Rat_instCoeFloat__batteries___closed__0;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_batteries_Batteries_Lean_Float(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_batteries_Batteries_Data_Rat_Float(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_batteries_Batteries_Lean_Float(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_batteries_Float_toRat0___closed__0 = _init_lp_batteries_Float_toRat0___closed__0();
lean_mark_persistent(lp_batteries_Float_toRat0___closed__0);
lp_batteries_Rat_instCoeFloat__batteries___closed__0 = _init_lp_batteries_Rat_instCoeFloat__batteries___closed__0();
lean_mark_persistent(lp_batteries_Rat_instCoeFloat__batteries___closed__0);
lp_batteries_Rat_instCoeFloat__batteries = _init_lp_batteries_Rat_instCoeFloat__batteries();
lean_mark_persistent(lp_batteries_Rat_instCoeFloat__batteries);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
