// Lean compiler output
// Module: Batteries.Data.Int
// Imports: public import Init public import Batteries.Data.Nat.Lemmas
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
LEAN_EXPORT uint8_t lp_batteries_Int_testBit(lean_object*, lean_object*);
static lean_object* lp_batteries___private_Batteries_Data_Int_0__Int_testBit_match__1_splitter___redArg___closed__0;
LEAN_EXPORT lean_object* lp_batteries_Fin_foldr_loop___at___00Int_ofBits_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Fin_foldr_loop___at___00Int_ofBits_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Bool_toNat(uint8_t);
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Data_Int_0__Int_testBit_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Data_Int_0__Int_testBit_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Data_Int_0__Int_testBit_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_subNatNat(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
uint8_t l_Nat_testBit(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Int_testBit___boxed(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Int_ofBits(lean_object*, lean_object*);
static lean_object* lp_batteries_Int_testBit___closed__0;
LEAN_EXPORT lean_object* lp_batteries_Fin_foldr_loop___at___00Int_ofBits_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Data_Int_0__Int_testBit_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_batteries_Int_testBit___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t lp_batteries_Int_testBit(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lp_batteries_Int_testBit___closed__0;
x_4 = lean_int_dec_lt(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_nat_abs(x_1);
x_6 = l_Nat_testBit(x_5, x_2);
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_nat_abs(x_1);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_7, x_8);
lean_dec(x_7);
x_10 = l_Nat_testBit(x_9, x_2);
lean_dec(x_9);
if (x_10 == 0)
{
return x_4;
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* lp_batteries_Int_testBit___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lp_batteries_Int_testBit(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_batteries_Fin_foldr_loop___at___00Int_ofBits_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 1)
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
lean_dec(x_2);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_mul(x_8, x_3);
lean_dec(x_3);
lean_inc_ref(x_1);
lean_inc(x_7);
x_10 = lean_apply_1(x_1, x_7);
x_11 = lean_unbox(x_10);
x_12 = l_Bool_toNat(x_11);
x_13 = lean_nat_add(x_9, x_12);
lean_dec(x_12);
lean_dec(x_9);
x_2 = x_7;
x_3 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* lp_batteries_Int_ofBits(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_5 = lp_batteries_Fin_foldr_loop___at___00Int_ofBits_spec__0___redArg(x_2, x_1, x_4);
x_6 = lean_nat_mul(x_3, x_5);
x_7 = lean_nat_pow(x_3, x_1);
lean_dec(x_1);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Int_subNatNat(x_5, x_7);
lean_dec(x_7);
lean_dec(x_5);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_7);
x_10 = lean_nat_to_int(x_5);
return x_10;
}
}
}
LEAN_EXPORT lean_object* lp_batteries_Fin_foldr_loop___at___00Int_ofBits_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_batteries_Fin_foldr_loop___at___00Int_ofBits_spec__0___redArg(x_1, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_batteries_Fin_foldr_loop___at___00Int_ofBits_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_batteries_Fin_foldr_loop___at___00Int_ofBits_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
static lean_object* _init_lp_batteries___private_Batteries_Data_Int_0__Int_testBit_match__1_splitter___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Data_Int_0__Int_testBit_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lp_batteries___private_Batteries_Data_Int_0__Int_testBit_match__1_splitter___redArg___closed__0;
x_6 = lean_int_dec_lt(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_7 = lean_nat_abs(x_1);
x_8 = lean_apply_2(x_3, x_7, x_2);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
x_9 = lean_nat_abs(x_1);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_9, x_10);
lean_dec(x_9);
x_12 = lean_apply_2(x_4, x_11, x_2);
return x_12;
}
}
}
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Data_Int_0__Int_testBit_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_batteries___private_Batteries_Data_Int_0__Int_testBit_match__1_splitter___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Data_Int_0__Int_testBit_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_batteries___private_Batteries_Data_Int_0__Int_testBit_match__1_splitter___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Data_Int_0__Int_testBit_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_batteries___private_Batteries_Data_Int_0__Int_testBit_match__1_splitter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_batteries_Batteries_Data_Nat_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_batteries_Batteries_Data_Int(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_batteries_Batteries_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_batteries_Int_testBit___closed__0 = _init_lp_batteries_Int_testBit___closed__0();
lean_mark_persistent(lp_batteries_Int_testBit___closed__0);
lp_batteries___private_Batteries_Data_Int_0__Int_testBit_match__1_splitter___redArg___closed__0 = _init_lp_batteries___private_Batteries_Data_Int_0__Int_testBit_match__1_splitter___redArg___closed__0();
lean_mark_persistent(lp_batteries___private_Batteries_Data_Int_0__Int_testBit_match__1_splitter___redArg___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
