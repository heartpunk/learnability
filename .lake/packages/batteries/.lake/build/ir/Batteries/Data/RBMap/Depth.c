// Lean compiler output
// Module: Batteries.Data.RBMap.Depth
// Imports: public import Init public import Batteries.Data.RBMap.WF
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
LEAN_EXPORT lean_object* lp_batteries_Batteries_RBNode_depth___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Data_RBMap_Depth_0__Batteries_RBNode_depth_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_RBNode_depthUB___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_RBNode_depthLB___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_RBNode_depthUB(uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Data_RBMap_Depth_0__Batteries_RBNode_depthLB_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Data_RBMap_Depth_0__Batteries_RBNode_depthLB_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Data_RBMap_Depth_0__Batteries_RBNode_depth_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Data_RBMap_Depth_0__Batteries_RBNode_depthLB_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_RBNode_depth___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_RBNode_depthLB(uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Data_RBMap_Depth_0__Batteries_RBNode_depthLB_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_RBNode_depth___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_RBNode_depth(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_RBNode_depth___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(0u);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 2);
x_9 = lp_batteries_Batteries_RBNode_depth___redArg(x_7);
x_10 = lp_batteries_Batteries_RBNode_depth___redArg(x_8);
x_11 = lean_nat_dec_le(x_9, x_10);
if (x_11 == 0)
{
lean_dec(x_10);
x_2 = x_9;
goto block_5;
}
else
{
lean_dec(x_9);
x_2 = x_10;
goto block_5;
}
}
block_5:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_add(x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_RBNode_depth___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_batteries_Batteries_RBNode_depth___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_RBNode_depth(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_batteries_Batteries_RBNode_depth___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_RBNode_depth___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_batteries_Batteries_RBNode_depth(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Data_RBMap_Depth_0__Batteries_RBNode_depth_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
lean_dec_ref(x_1);
x_10 = lean_box(x_6);
x_11 = lean_apply_4(x_3, x_10, x_7, x_8, x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Data_RBMap_Depth_0__Batteries_RBNode_depth_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_batteries___private_Batteries_Data_RBMap_Depth_0__Batteries_RBNode_depth_match__1_splitter___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_RBNode_depthLB(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_add(x_2, x_3);
return x_4;
}
else
{
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_RBNode_depthLB___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = lp_batteries_Batteries_RBNode_depthLB(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_RBNode_depthUB(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_3, x_2);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_4, x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(2u);
x_8 = lean_nat_mul(x_7, x_2);
return x_8;
}
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_RBNode_depthUB___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = lp_batteries_Batteries_RBNode_depthUB(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Data_RBMap_Depth_0__Batteries_RBNode_depthLB_match__1_splitter___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (x_1 == 0)
{
lean_object* x_5; 
lean_dec(x_4);
x_5 = lean_apply_1(x_3, x_2);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_apply_1(x_4, x_2);
return x_6;
}
}
}
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Data_RBMap_Depth_0__Batteries_RBNode_depthLB_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
x_6 = lp_batteries___private_Batteries_Data_RBMap_Depth_0__Batteries_RBNode_depthLB_match__1_splitter___redArg(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Data_RBMap_Depth_0__Batteries_RBNode_depthLB_match__1_splitter(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_batteries___private_Batteries_Data_RBMap_Depth_0__Batteries_RBNode_depthLB_match__1_splitter___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Data_RBMap_Depth_0__Batteries_RBNode_depthLB_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = lp_batteries___private_Batteries_Data_RBMap_Depth_0__Batteries_RBNode_depthLB_match__1_splitter(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_batteries_Batteries_Data_RBMap_WF(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_batteries_Batteries_Data_RBMap_Depth(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_batteries_Batteries_Data_RBMap_WF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
