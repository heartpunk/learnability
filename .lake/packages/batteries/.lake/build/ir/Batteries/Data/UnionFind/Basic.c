// Lean compiler output
// Module: Batteries.Data.UnionFind.Basic
// Imports: public import Init public import Batteries.Tactic.Lint.Misc public import Batteries.Tactic.SeqFocus public import Batteries.Util.Panic
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
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_findD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_empty;
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_unionN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_findN___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_checkEquivN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_push(lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_rankD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_checkEquiv_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_root___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_checkEquivN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_rank(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_rootN___redArg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_checkEquivN___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_findAux(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_instEmptyCollection;
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_findN(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_unionN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_parentD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_rootD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_root_x21___boxed(lean_object*, lean_object*);
static lean_object* lp_batteries_Batteries_UnionFind_empty___closed__0;
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_linkAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_findN___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_parentD___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_root(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_checkEquivD(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_rank___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_link(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_rankD___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_rootN___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_unionN___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_link_x21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_link_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_rootD___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_rootN___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_linkN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_mkEmpty(lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_checkEquiv(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_link___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_union_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_linkN___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_batteries_panic___at___00Batteries_panicWith_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_root_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_parent___boxed(lean_object*, lean_object*);
static lean_object* lp_batteries_Batteries_UnionFind_root_x21___closed__0;
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Data_UnionFind_Basic_0__Batteries_UnionFind_findAux_match__1_splitter___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_find_x21(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_rootN(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_mkEmpty___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_size___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_size(lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_parent(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Data_UnionFind_Basic_0__Batteries_UnionFind_findAux_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Data_UnionFind_Basic_0__Batteries_UnionFind_findAux_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_linkN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_union(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_parentD(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_array_fget_borrowed(x_1, x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
return x_6;
}
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_parentD___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_batteries_Batteries_UnionFind_parentD(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_rankD(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(0u);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_fget_borrowed(x_1, x_2);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
return x_7;
}
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_rankD___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_batteries_Batteries_UnionFind_rankD(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_size(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_size___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_batteries_Batteries_UnionFind_size(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_mkEmpty(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_mkEmpty___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_batteries_Batteries_UnionFind_mkEmpty(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_lp_batteries_Batteries_UnionFind_empty___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_lp_batteries_Batteries_UnionFind_empty() {
_start:
{
lean_object* x_1; 
x_1 = lp_batteries_Batteries_UnionFind_empty___closed__0;
return x_1;
}
}
static lean_object* _init_lp_batteries_Batteries_UnionFind_instEmptyCollection() {
_start:
{
lean_object* x_1; 
x_1 = lp_batteries_Batteries_UnionFind_empty;
return x_1;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_parent(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_batteries_Batteries_UnionFind_parentD(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_parent___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_batteries_Batteries_UnionFind_parent(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_rank(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_batteries_Batteries_UnionFind_rankD(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_rank___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_batteries_Batteries_UnionFind_rank(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_push(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_array_push(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_root(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_fget_borrowed(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_nat_dec_eq(x_4, x_2);
if (x_5 == 0)
{
lean_dec(x_2);
lean_inc(x_4);
x_2 = x_4;
goto _start;
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_root___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_batteries_Batteries_UnionFind_root(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_rootN___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_batteries_Batteries_UnionFind_root(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_rootN___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_batteries_Batteries_UnionFind_rootN___redArg(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_rootN(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_batteries_Batteries_UnionFind_root(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_rootN___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_batteries_Batteries_UnionFind_rootN(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_lp_batteries_Batteries_UnionFind_root_x21___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("index out of bounds", 19, 19);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_root_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lp_batteries_Batteries_UnionFind_root_x21___closed__0;
x_6 = lp_batteries_panic___at___00Batteries_panicWith_spec__0(lean_box(0), x_2, x_5);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lp_batteries_Batteries_UnionFind_root(x_1, x_2);
return x_7;
}
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_root_x21___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_batteries_Batteries_UnionFind_root_x21(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_rootD(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
return x_2;
}
else
{
lean_object* x_5; 
x_5 = lp_batteries_Batteries_UnionFind_root(x_1, x_2);
return x_5;
}
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_rootD___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_batteries_Batteries_UnionFind_rootD(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_findAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_fget(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_dec(x_6);
x_7 = lean_nat_dec_eq(x_5, x_2);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
lean_free_object(x_3);
x_8 = lp_batteries_Batteries_UnionFind_findAux(x_1, x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_array_get_size(x_10);
x_13 = lean_nat_dec_lt(x_2, x_12);
if (x_13 == 0)
{
lean_dec(x_2);
return x_8;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_fget(x_10, x_2);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_box(0);
x_18 = lean_array_fset(x_10, x_2, x_17);
lean_inc(x_11);
lean_ctor_set(x_14, 0, x_11);
x_19 = lean_array_fset(x_18, x_2, x_14);
lean_dec(x_2);
lean_ctor_set(x_8, 0, x_19);
return x_8;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_box(0);
x_22 = lean_array_fset(x_10, x_2, x_21);
lean_inc(x_11);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_11);
lean_ctor_set(x_23, 1, x_20);
x_24 = lean_array_fset(x_22, x_2, x_23);
lean_dec(x_2);
lean_ctor_set(x_8, 0, x_24);
return x_8;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_8, 0);
x_26 = lean_ctor_get(x_8, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_8);
x_27 = lean_array_get_size(x_25);
x_28 = lean_nat_dec_lt(x_2, x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_2);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_array_fget(x_25, x_2);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
x_33 = lean_box(0);
x_34 = lean_array_fset(x_25, x_2, x_33);
lean_inc(x_26);
if (lean_is_scalar(x_32)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_32;
}
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_31);
x_36 = lean_array_fset(x_34, x_2, x_35);
lean_dec(x_2);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_26);
return x_37;
}
}
}
else
{
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_3, 0);
lean_inc(x_38);
lean_dec(x_3);
x_39 = lean_nat_dec_eq(x_38, x_2);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_40 = lp_batteries_Batteries_UnionFind_findAux(x_1, x_38);
x_41 = lean_ctor_get(x_40, 0);
lean_inc_ref(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_43 = x_40;
} else {
 lean_dec_ref(x_40);
 x_43 = lean_box(0);
}
x_44 = lean_array_get_size(x_41);
x_45 = lean_nat_dec_lt(x_2, x_44);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_2);
if (lean_is_scalar(x_43)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_43;
}
lean_ctor_set(x_46, 0, x_41);
lean_ctor_set(x_46, 1, x_42);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_47 = lean_array_fget(x_41, x_2);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_49 = x_47;
} else {
 lean_dec_ref(x_47);
 x_49 = lean_box(0);
}
x_50 = lean_box(0);
x_51 = lean_array_fset(x_41, x_2, x_50);
lean_inc(x_42);
if (lean_is_scalar(x_49)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_49;
}
lean_ctor_set(x_52, 0, x_42);
lean_ctor_set(x_52, 1, x_48);
x_53 = lean_array_fset(x_51, x_2, x_52);
lean_dec(x_2);
if (lean_is_scalar(x_43)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_43;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_42);
return x_54;
}
}
else
{
lean_object* x_55; 
lean_dec(x_38);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_2);
return x_55;
}
}
}
}
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Data_UnionFind_Basic_0__Batteries_UnionFind_findAux_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_3(x_2, x_3, x_4, lean_box(0));
return x_5;
}
}
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Data_UnionFind_Basic_0__Batteries_UnionFind_findAux_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_batteries___private_Batteries_Data_UnionFind_Basic_0__Batteries_UnionFind_findAux_match__1_splitter___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_batteries___private_Batteries_Data_UnionFind_Basic_0__Batteries_UnionFind_findAux_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_batteries___private_Batteries_Data_UnionFind_Basic_0__Batteries_UnionFind_findAux_match__1_splitter(x_1, x_2, x_3, x_4);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_find(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lp_batteries_Batteries_UnionFind_findAux(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_findN___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lp_batteries_Batteries_UnionFind_find(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_findN(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_batteries_Batteries_UnionFind_findN___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_findN___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_batteries_Batteries_UnionFind_findN(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_find_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
x_6 = lp_batteries_Batteries_UnionFind_root_x21___closed__0;
x_7 = lp_batteries_panic___at___00Batteries_panicWith_spec__0(lean_box(0), x_5, x_6);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lp_batteries_Batteries_UnionFind_find(x_1, x_2);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_findD(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lp_batteries_Batteries_UnionFind_find(x_1, x_2);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_linkAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_fget(x_1, x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_array_fget(x_1, x_2);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 1);
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_nat_dec_lt(x_8, x_11);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
lean_inc(x_11);
lean_inc(x_3);
lean_ctor_set(x_9, 0, x_3);
x_14 = lean_array_fset(x_1, x_2, x_9);
lean_dec(x_2);
x_15 = lean_nat_dec_eq(x_11, x_8);
lean_dec(x_11);
if (x_15 == 0)
{
lean_free_object(x_5);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_8, x_16);
lean_dec(x_8);
lean_ctor_set(x_5, 1, x_17);
x_18 = lean_array_fset(x_14, x_3, x_5);
lean_dec(x_3);
return x_18;
}
}
else
{
lean_object* x_19; 
lean_dec(x_11);
lean_free_object(x_5);
lean_dec(x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 0, x_2);
x_19 = lean_array_fset(x_1, x_3, x_9);
lean_dec(x_3);
return x_19;
}
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_dec(x_9);
x_21 = lean_nat_dec_lt(x_8, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_inc(x_20);
lean_inc(x_3);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_3);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_array_fset(x_1, x_2, x_22);
lean_dec(x_2);
x_24 = lean_nat_dec_eq(x_20, x_8);
lean_dec(x_20);
if (x_24 == 0)
{
lean_free_object(x_5);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
return x_23;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_8, x_25);
lean_dec(x_8);
lean_ctor_set(x_5, 1, x_26);
x_27 = lean_array_fset(x_23, x_3, x_5);
lean_dec(x_3);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_20);
lean_free_object(x_5);
lean_dec(x_7);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_8);
x_29 = lean_array_fset(x_1, x_3, x_28);
lean_dec(x_3);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_ctor_get(x_5, 0);
x_31 = lean_ctor_get(x_5, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_5);
x_32 = lean_array_fget(x_1, x_2);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_34 = x_32;
} else {
 lean_dec_ref(x_32);
 x_34 = lean_box(0);
}
x_35 = lean_nat_dec_lt(x_31, x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_inc(x_33);
lean_inc(x_3);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_3);
lean_ctor_set(x_36, 1, x_33);
x_37 = lean_array_fset(x_1, x_2, x_36);
lean_dec(x_2);
x_38 = lean_nat_dec_eq(x_33, x_31);
lean_dec(x_33);
if (x_38 == 0)
{
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_3);
return x_37;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_31, x_39);
lean_dec(x_31);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_30);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_array_fset(x_37, x_3, x_41);
lean_dec(x_3);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_33);
lean_dec(x_30);
if (lean_is_scalar(x_34)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_34;
}
lean_ctor_set(x_43, 0, x_2);
lean_ctor_set(x_43, 1, x_31);
x_44 = lean_array_fset(x_1, x_3, x_43);
lean_dec(x_3);
return x_44;
}
}
}
else
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_link___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_batteries_Batteries_UnionFind_linkAux(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_link(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_batteries_Batteries_UnionFind_linkAux(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_linkN___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_batteries_Batteries_UnionFind_linkAux(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_linkN(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_batteries_Batteries_UnionFind_linkAux(x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_linkN___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_batteries_Batteries_UnionFind_linkN(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_link_x21___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_1);
x_8 = lean_nat_dec_lt(x_2, x_7);
if (x_8 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
goto block_6;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_3, x_7);
if (x_9 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
goto block_6;
}
else
{
lean_object* x_10; 
x_10 = lp_batteries_Batteries_UnionFind_linkAux(x_1, x_2, x_3);
return x_10;
}
}
block_6:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lp_batteries_Batteries_UnionFind_root_x21___closed__0;
x_5 = lp_batteries_panic___at___00Batteries_panicWith_spec__0(lean_box(0), x_1, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_link_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_batteries_Batteries_UnionFind_link_x21___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_union(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lp_batteries_Batteries_UnionFind_find(x_1, x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lp_batteries_Batteries_UnionFind_find(x_5, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = lp_batteries_Batteries_UnionFind_linkAux(x_8, x_6, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_unionN___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_batteries_Batteries_UnionFind_union(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_unionN(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_batteries_Batteries_UnionFind_union(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_unionN___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_batteries_Batteries_UnionFind_unionN(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_union_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_1);
x_8 = lean_nat_dec_lt(x_2, x_7);
if (x_8 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
goto block_6;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_3, x_7);
if (x_9 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
goto block_6;
}
else
{
lean_object* x_10; 
x_10 = lp_batteries_Batteries_UnionFind_union(x_1, x_2, x_3);
return x_10;
}
}
block_6:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lp_batteries_Batteries_UnionFind_root_x21___closed__0;
x_5 = lp_batteries_panic___at___00Batteries_panicWith_spec__0(lean_box(0), x_1, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_checkEquiv(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lp_batteries_Batteries_UnionFind_find(x_1, x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lp_batteries_Batteries_UnionFind_find(x_5, x_3);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 1);
x_10 = lean_nat_dec_eq(x_6, x_9);
lean_dec(x_9);
lean_dec(x_6);
x_11 = lean_box(x_10);
lean_ctor_set(x_7, 1, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = lean_nat_dec_eq(x_6, x_13);
lean_dec(x_13);
lean_dec(x_6);
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_checkEquivN___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_batteries_Batteries_UnionFind_checkEquiv(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_checkEquivN(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_batteries_Batteries_UnionFind_checkEquiv(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_checkEquivN___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_batteries_Batteries_UnionFind_checkEquivN(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_checkEquiv_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_1);
x_11 = lean_nat_dec_lt(x_2, x_10);
if (x_11 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
goto block_9;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_lt(x_3, x_10);
if (x_12 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
goto block_9;
}
else
{
lean_object* x_13; 
x_13 = lp_batteries_Batteries_UnionFind_checkEquiv(x_1, x_2, x_3);
return x_13;
}
}
block_9:
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = 0;
x_5 = lean_box(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
x_7 = lp_batteries_Batteries_UnionFind_root_x21___closed__0;
x_8 = lp_batteries_panic___at___00Batteries_panicWith_spec__0(lean_box(0), x_6, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* lp_batteries_Batteries_UnionFind_checkEquivD(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lp_batteries_Batteries_UnionFind_findD(x_1, x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lp_batteries_Batteries_UnionFind_findD(x_5, x_3);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 1);
x_10 = lean_nat_dec_eq(x_6, x_9);
lean_dec(x_9);
lean_dec(x_6);
x_11 = lean_box(x_10);
lean_ctor_set(x_7, 1, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = lean_nat_dec_eq(x_6, x_13);
lean_dec(x_13);
lean_dec(x_6);
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_batteries_Batteries_Tactic_Lint_Misc(uint8_t builtin);
lean_object* initialize_batteries_Batteries_Tactic_SeqFocus(uint8_t builtin);
lean_object* initialize_batteries_Batteries_Util_Panic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_batteries_Batteries_Data_UnionFind_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_batteries_Batteries_Tactic_Lint_Misc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_batteries_Batteries_Tactic_SeqFocus(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_batteries_Batteries_Util_Panic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_batteries_Batteries_UnionFind_empty___closed__0 = _init_lp_batteries_Batteries_UnionFind_empty___closed__0();
lean_mark_persistent(lp_batteries_Batteries_UnionFind_empty___closed__0);
lp_batteries_Batteries_UnionFind_empty = _init_lp_batteries_Batteries_UnionFind_empty();
lean_mark_persistent(lp_batteries_Batteries_UnionFind_empty);
lp_batteries_Batteries_UnionFind_instEmptyCollection = _init_lp_batteries_Batteries_UnionFind_instEmptyCollection();
lean_mark_persistent(lp_batteries_Batteries_UnionFind_instEmptyCollection);
lp_batteries_Batteries_UnionFind_root_x21___closed__0 = _init_lp_batteries_Batteries_UnionFind_root_x21___closed__0();
lean_mark_persistent(lp_batteries_Batteries_UnionFind_root_x21___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
