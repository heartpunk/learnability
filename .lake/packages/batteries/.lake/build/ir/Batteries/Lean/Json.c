// Lean compiler output
// Module: Batteries.Lean.Json
// Imports: public import Init public import Batteries.Lean.Float public import Lean.Data.Json.FromToJson.Basic
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
static lean_object* lp_batteries_instToJsonFloat__batteries___lam__0___closed__0;
LEAN_EXPORT lean_object* lp_batteries_instOfScientificJsonNumber__batteries___lam__0(lean_object*, uint8_t, lean_object*);
lean_object* l_instNatCastInt___lam__0(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* lp_batteries_instToJsonFloat__batteries;
LEAN_EXPORT lean_object* lp_batteries_instOfScientificJsonNumber__batteries___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_instNegJsonNumber__batteries;
LEAN_EXPORT lean_object* lp_batteries_instNegJsonNumber__batteries___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_batteries_instToJsonFloat__batteries___lam__0(double);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
static lean_object* lp_batteries_instOfScientificJsonNumber__batteries___closed__0;
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* lp_batteries_instToJsonFloat__batteries___closed__0;
LEAN_EXPORT lean_object* lp_batteries_instOfScientificJsonNumber__batteries;
lean_object* lean_int_neg(lean_object*);
static lean_object* lp_batteries_instNegJsonNumber__batteries___closed__0;
LEAN_EXPORT lean_object* lp_batteries_instToJsonFloat__batteries___lam__0___boxed(lean_object*);
lean_object* lp_batteries_Float_toRatParts_x27(double);
LEAN_EXPORT lean_object* lp_batteries_instOfScientificJsonNumber__batteries___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (x_2 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_unsigned_to_nat(10u);
x_5 = lean_nat_pow(x_4, x_3);
lean_dec(x_3);
x_6 = lean_nat_mul(x_1, x_5);
lean_dec(x_5);
lean_dec(x_1);
x_7 = l_instNatCastInt___lam__0(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_instNatCastInt___lam__0(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
}
}
LEAN_EXPORT lean_object* lp_batteries_instOfScientificJsonNumber__batteries___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
x_5 = lp_batteries_instOfScientificJsonNumber__batteries___lam__0(x_1, x_4, x_3);
return x_5;
}
}
static lean_object* _init_lp_batteries_instOfScientificJsonNumber__batteries___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lp_batteries_instOfScientificJsonNumber__batteries___lam__0___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_lp_batteries_instOfScientificJsonNumber__batteries() {
_start:
{
lean_object* x_1; 
x_1 = lp_batteries_instOfScientificJsonNumber__batteries___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* lp_batteries_instNegJsonNumber__batteries___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_int_neg(x_3);
lean_dec(x_3);
lean_ctor_set(x_1, 0, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = lean_int_neg(x_5);
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
}
static lean_object* _init_lp_batteries_instNegJsonNumber__batteries___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lp_batteries_instNegJsonNumber__batteries___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_lp_batteries_instNegJsonNumber__batteries() {
_start:
{
lean_object* x_1; 
x_1 = lp_batteries_instNegJsonNumber__batteries___closed__0;
return x_1;
}
}
static lean_object* _init_lp_batteries_instToJsonFloat__batteries___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_batteries_instToJsonFloat__batteries___lam__0(double x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_batteries_Float_toRatParts_x27(x_1);
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
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lp_batteries_instToJsonFloat__batteries___lam__0___closed__0;
x_11 = lean_int_dec_lt(x_8, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_nat_abs(x_8);
lean_dec(x_8);
x_14 = lean_nat_pow(x_12, x_13);
lean_dec(x_13);
x_15 = l_instNatCastInt___lam__0(x_14);
x_16 = lean_int_mul(x_7, x_15);
lean_dec(x_15);
lean_dec(x_7);
lean_ctor_set(x_5, 1, x_9);
lean_ctor_set(x_5, 0, x_16);
lean_ctor_set_tag(x_2, 2);
return x_2;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_unsigned_to_nat(5u);
x_18 = lean_nat_abs(x_8);
lean_dec(x_8);
x_19 = lean_nat_pow(x_17, x_18);
x_20 = l_instNatCastInt___lam__0(x_19);
x_21 = lean_int_mul(x_7, x_20);
lean_dec(x_20);
lean_dec(x_7);
lean_ctor_set(x_5, 1, x_18);
lean_ctor_set(x_5, 0, x_21);
lean_ctor_set_tag(x_2, 2);
return x_2;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_5, 0);
x_23 = lean_ctor_get(x_5, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_5);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lp_batteries_instToJsonFloat__batteries___lam__0___closed__0;
x_26 = lean_int_dec_lt(x_23, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_unsigned_to_nat(2u);
x_28 = lean_nat_abs(x_23);
lean_dec(x_23);
x_29 = lean_nat_pow(x_27, x_28);
lean_dec(x_28);
x_30 = l_instNatCastInt___lam__0(x_29);
x_31 = lean_int_mul(x_22, x_30);
lean_dec(x_30);
lean_dec(x_22);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_24);
lean_ctor_set_tag(x_2, 2);
lean_ctor_set(x_2, 0, x_32);
return x_2;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_unsigned_to_nat(5u);
x_34 = lean_nat_abs(x_23);
lean_dec(x_23);
x_35 = lean_nat_pow(x_33, x_34);
x_36 = l_instNatCastInt___lam__0(x_35);
x_37 = lean_int_mul(x_22, x_36);
lean_dec(x_36);
lean_dec(x_22);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set_tag(x_2, 2);
lean_ctor_set(x_2, 0, x_38);
return x_2;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_39 = lean_ctor_get(x_2, 0);
lean_inc(x_39);
lean_dec(x_2);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
x_43 = lean_unsigned_to_nat(0u);
x_44 = lp_batteries_instToJsonFloat__batteries___lam__0___closed__0;
x_45 = lean_int_dec_lt(x_41, x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_46 = lean_unsigned_to_nat(2u);
x_47 = lean_nat_abs(x_41);
lean_dec(x_41);
x_48 = lean_nat_pow(x_46, x_47);
lean_dec(x_47);
x_49 = l_instNatCastInt___lam__0(x_48);
x_50 = lean_int_mul(x_40, x_49);
lean_dec(x_49);
lean_dec(x_40);
if (lean_is_scalar(x_42)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_42;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_43);
x_52 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_53 = lean_unsigned_to_nat(5u);
x_54 = lean_nat_abs(x_41);
lean_dec(x_41);
x_55 = lean_nat_pow(x_53, x_54);
x_56 = l_instNatCastInt___lam__0(x_55);
x_57 = lean_int_mul(x_40, x_56);
lean_dec(x_56);
lean_dec(x_40);
if (lean_is_scalar(x_42)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_42;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_54);
x_59 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_batteries_instToJsonFloat__batteries___lam__0___boxed(lean_object* x_1) {
_start:
{
double x_2; lean_object* x_3; 
x_2 = lean_unbox_float(x_1);
lean_dec_ref(x_1);
x_3 = lp_batteries_instToJsonFloat__batteries___lam__0(x_2);
return x_3;
}
}
static lean_object* _init_lp_batteries_instToJsonFloat__batteries___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lp_batteries_instToJsonFloat__batteries___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_lp_batteries_instToJsonFloat__batteries() {
_start:
{
lean_object* x_1; 
x_1 = lp_batteries_instToJsonFloat__batteries___closed__0;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_batteries_Batteries_Lean_Float(uint8_t builtin);
lean_object* initialize_Lean_Data_Json_FromToJson_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_batteries_Batteries_Lean_Json(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_batteries_Batteries_Lean_Float(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json_FromToJson_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_batteries_instOfScientificJsonNumber__batteries___closed__0 = _init_lp_batteries_instOfScientificJsonNumber__batteries___closed__0();
lean_mark_persistent(lp_batteries_instOfScientificJsonNumber__batteries___closed__0);
lp_batteries_instOfScientificJsonNumber__batteries = _init_lp_batteries_instOfScientificJsonNumber__batteries();
lean_mark_persistent(lp_batteries_instOfScientificJsonNumber__batteries);
lp_batteries_instNegJsonNumber__batteries___closed__0 = _init_lp_batteries_instNegJsonNumber__batteries___closed__0();
lean_mark_persistent(lp_batteries_instNegJsonNumber__batteries___closed__0);
lp_batteries_instNegJsonNumber__batteries = _init_lp_batteries_instNegJsonNumber__batteries();
lean_mark_persistent(lp_batteries_instNegJsonNumber__batteries);
lp_batteries_instToJsonFloat__batteries___lam__0___closed__0 = _init_lp_batteries_instToJsonFloat__batteries___lam__0___closed__0();
lean_mark_persistent(lp_batteries_instToJsonFloat__batteries___lam__0___closed__0);
lp_batteries_instToJsonFloat__batteries___closed__0 = _init_lp_batteries_instToJsonFloat__batteries___closed__0();
lean_mark_persistent(lp_batteries_instToJsonFloat__batteries___closed__0);
lp_batteries_instToJsonFloat__batteries = _init_lp_batteries_instToJsonFloat__batteries();
lean_mark_persistent(lp_batteries_instToJsonFloat__batteries);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
