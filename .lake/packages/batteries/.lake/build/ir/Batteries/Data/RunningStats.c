// Lean compiler output
// Module: Batteries.Data.RunningStats
// Imports: public import Init public import Init.Data.Nat
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
double lean_float_mul(double, double);
double lean_float_div(double, double);
LEAN_EXPORT lean_object* lp_batteries_Batteries_RunningStats_variance___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_RunningStats_push___boxed(lean_object*, lean_object*);
double sqrt(double);
LEAN_EXPORT lean_object* lp_batteries_Batteries_RunningStats_sampleVariance___boxed(lean_object*);
double lean_float_add(double, double);
LEAN_EXPORT double lp_batteries_Batteries_RunningStats_variance(lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_RunningStats_standardDeviation___boxed(lean_object*);
double lean_float_of_nat(lean_object*);
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_RunningStats_push(double, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT double lp_batteries_Batteries_RunningStats_standardDeviation(lean_object*);
LEAN_EXPORT double lp_batteries_Batteries_RunningStats_sampleVariance(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
double lean_float_sub(double, double);
LEAN_EXPORT lean_object* lp_batteries_Batteries_RunningStats_push(double x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; double x_5; double x_6; lean_object* x_7; lean_object* x_8; double x_9; double x_10; double x_11; double x_12; double x_13; double x_14; double x_15; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get_float(x_2, sizeof(void*)*1);
x_6 = lean_ctor_get_float(x_2, sizeof(void*)*1 + 8);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_4, x_7);
lean_dec(x_4);
x_9 = lean_float_sub(x_1, x_5);
lean_inc(x_8);
x_10 = lean_float_of_nat(x_8);
x_11 = lean_float_div(x_9, x_10);
x_12 = lean_float_add(x_5, x_11);
x_13 = lean_float_sub(x_1, x_12);
x_14 = lean_float_mul(x_9, x_13);
x_15 = lean_float_add(x_6, x_14);
lean_ctor_set(x_2, 0, x_8);
lean_ctor_set_float(x_2, sizeof(void*)*1, x_12);
lean_ctor_set_float(x_2, sizeof(void*)*1 + 8, x_15);
return x_2;
}
else
{
lean_object* x_16; double x_17; double x_18; lean_object* x_19; lean_object* x_20; double x_21; double x_22; double x_23; double x_24; double x_25; double x_26; double x_27; lean_object* x_28; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_ctor_get_float(x_2, sizeof(void*)*1);
x_18 = lean_ctor_get_float(x_2, sizeof(void*)*1 + 8);
lean_inc(x_16);
lean_dec(x_2);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_16, x_19);
lean_dec(x_16);
x_21 = lean_float_sub(x_1, x_17);
lean_inc(x_20);
x_22 = lean_float_of_nat(x_20);
x_23 = lean_float_div(x_21, x_22);
x_24 = lean_float_add(x_17, x_23);
x_25 = lean_float_sub(x_1, x_24);
x_26 = lean_float_mul(x_21, x_25);
x_27 = lean_float_add(x_18, x_26);
x_28 = lean_alloc_ctor(0, 1, 16);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set_float(x_28, sizeof(void*)*1, x_24);
lean_ctor_set_float(x_28, sizeof(void*)*1 + 8, x_27);
return x_28;
}
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_RunningStats_push___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
double x_3; lean_object* x_4; 
x_3 = lean_unbox_float(x_1);
lean_dec_ref(x_1);
x_4 = lp_batteries_Batteries_RunningStats_push(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT double lp_batteries_Batteries_RunningStats_variance(lean_object* x_1) {
_start:
{
lean_object* x_2; double x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get_float(x_1, sizeof(void*)*1 + 8);
lean_dec_ref(x_1);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_dec_le(x_2, x_4);
if (x_5 == 0)
{
double x_6; double x_7; 
x_6 = lean_float_of_nat(x_2);
x_7 = lean_float_div(x_3, x_6);
return x_7;
}
else
{
lean_object* x_8; double x_9; 
lean_dec(x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Float_ofScientific(x_8, x_5, x_4);
return x_9;
}
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_RunningStats_variance___boxed(lean_object* x_1) {
_start:
{
double x_2; lean_object* x_3; 
x_2 = lp_batteries_Batteries_RunningStats_variance(x_1);
x_3 = lean_box_float(x_2);
return x_3;
}
}
LEAN_EXPORT double lp_batteries_Batteries_RunningStats_sampleVariance(lean_object* x_1) {
_start:
{
lean_object* x_2; double x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get_float(x_1, sizeof(void*)*1 + 8);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_dec_le(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; double x_8; double x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
x_8 = lean_float_of_nat(x_7);
x_9 = lean_float_div(x_3, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; double x_12; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Float_ofScientific(x_10, x_5, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_RunningStats_sampleVariance___boxed(lean_object* x_1) {
_start:
{
double x_2; lean_object* x_3; 
x_2 = lp_batteries_Batteries_RunningStats_sampleVariance(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_float(x_2);
return x_3;
}
}
LEAN_EXPORT double lp_batteries_Batteries_RunningStats_standardDeviation(lean_object* x_1) {
_start:
{
lean_object* x_2; double x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get_float(x_1, sizeof(void*)*1 + 8);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_dec_le(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; double x_8; double x_9; double x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
x_8 = lean_float_of_nat(x_7);
x_9 = lean_float_div(x_3, x_8);
x_10 = sqrt(x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; double x_13; double x_14; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Float_ofScientific(x_11, x_5, x_12);
x_14 = sqrt(x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_RunningStats_standardDeviation___boxed(lean_object* x_1) {
_start:
{
double x_2; lean_object* x_3; 
x_2 = lp_batteries_Batteries_RunningStats_standardDeviation(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_float(x_2);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init_Data_Nat(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_batteries_Batteries_Data_RunningStats(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
