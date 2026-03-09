// Lean compiler output
// Module: Batteries.Lean.IO.Process
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_io_prim_handle_put_str(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_IO_Process_runCmdWithInput_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_IO_Process_runCmdWithInput_x27___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_flush(lean_object*);
lean_object* lean_io_process_child_take_stdin(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_IO_ofExcept___at___00IO_Process_runCmdWithInput_x27_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_IO_Process_runCmdWithInput_x27___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_batteries_IO_Process_runCmdWithInput___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_IO_Process_runCmdWithInput_x27(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* lp_batteries_IO_Process_runCmdWithInput_x27___closed__2;
static lean_object* lp_batteries_IO_Process_runCmdWithInput_x27___closed__1;
lean_object* lean_io_process_child_wait(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_IO_Process_runCmdWithInput(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_io_process_spawn(lean_object*);
LEAN_EXPORT lean_object* lp_batteries_IO_ofExcept___at___00IO_Process_runCmdWithInput_x27_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_task_get_own(lean_object*);
static lean_object* lp_batteries_IO_Process_runCmdWithInput_x27___closed__0;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* lp_batteries_IO_ofExcept___at___00IO_Process_runCmdWithInput_x27_spec__0___redArg(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_IO_FS_Handle_readToEnd(lean_object*);
LEAN_EXPORT lean_object* lp_batteries_IO_ofExcept___at___00IO_Process_runCmdWithInput_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_batteries_IO_ofExcept___at___00IO_Process_runCmdWithInput_x27_spec__0___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_io_error_to_string(x_4);
x_6 = lean_mk_io_user_error(x_5);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_io_error_to_string(x_7);
x_9 = lean_mk_io_user_error(x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_ctor_set_tag(x_1, 0);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* lp_batteries_IO_ofExcept___at___00IO_Process_runCmdWithInput_x27_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_batteries_IO_ofExcept___at___00IO_Process_runCmdWithInput_x27_spec__0___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_batteries_IO_ofExcept___at___00IO_Process_runCmdWithInput_x27_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = lp_batteries_IO_ofExcept___at___00IO_Process_runCmdWithInput_x27_spec__0___redArg(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_batteries_IO_ofExcept___at___00IO_Process_runCmdWithInput_x27_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_batteries_IO_ofExcept___at___00IO_Process_runCmdWithInput_x27_spec__0(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_batteries_IO_Process_runCmdWithInput_x27___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Handle_readToEnd(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_ctor_set_tag(x_3, 1);
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_ctor_set_tag(x_3, 0);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* lp_batteries_IO_Process_runCmdWithInput_x27___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_batteries_IO_Process_runCmdWithInput_x27___lam__0(x_1);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_lp_batteries_IO_Process_runCmdWithInput_x27___closed__0() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_2, 0, x_1);
lean_ctor_set_uint8(x_2, 1, x_1);
lean_ctor_set_uint8(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_lp_batteries_IO_Process_runCmdWithInput_x27___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_lp_batteries_IO_Process_runCmdWithInput_x27___closed__2() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; 
x_1 = 0;
x_2 = 2;
x_3 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, 1, x_1);
lean_ctor_set_uint8(x_3, 2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_batteries_IO_Process_runCmdWithInput_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lp_batteries_IO_Process_runCmdWithInput_x27___closed__0;
x_7 = lean_box(0);
x_8 = lp_batteries_IO_Process_runCmdWithInput_x27___closed__1;
x_9 = 1;
x_10 = 0;
x_11 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_1);
lean_ctor_set(x_11, 2, x_2);
lean_ctor_set(x_11, 3, x_7);
lean_ctor_set(x_11, 4, x_8);
lean_ctor_set_uint8(x_11, sizeof(void*)*5, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*5 + 1, x_10);
x_12 = lean_io_process_spawn(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_io_process_child_take_stdin(x_6, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_io_prim_handle_put_str(x_16, x_3);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
lean_dec_ref(x_18);
x_19 = lean_io_prim_handle_flush(x_16);
lean_dec(x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec_ref(x_19);
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_ctor_get(x_17, 2);
lean_inc(x_20);
x_22 = lean_alloc_closure((void*)(lp_batteries_IO_Process_runCmdWithInput_x27___lam__0___boxed), 2, 1);
lean_closure_set(x_22, 0, x_20);
x_23 = lean_unsigned_to_nat(9u);
x_24 = lean_io_as_task(x_22, x_23);
x_25 = l_IO_FS_Handle_readToEnd(x_21);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = lp_batteries_IO_Process_runCmdWithInput_x27___closed__2;
x_28 = lean_io_process_child_wait(x_27, x_17);
lean_dec(x_17);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; uint32_t x_45; uint32_t x_46; uint8_t x_47; 
x_30 = lean_ctor_get(x_28, 0);
x_45 = 0;
x_46 = lean_unbox_uint32(x_30);
x_47 = lean_uint32_dec_eq(x_46, x_45);
if (x_47 == 0)
{
if (x_4 == 0)
{
lean_free_object(x_28);
goto block_44;
}
else
{
lean_object* x_48; 
lean_dec(x_30);
lean_dec_ref(x_24);
x_48 = lean_mk_io_user_error(x_26);
lean_ctor_set_tag(x_28, 1);
lean_ctor_set(x_28, 0, x_48);
return x_28;
}
}
else
{
lean_free_object(x_28);
goto block_44;
}
block_44:
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_task_get_own(x_24);
x_32 = lp_batteries_IO_ofExcept___at___00IO_Process_runCmdWithInput_x27_spec__0___redArg(x_31);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; uint32_t x_36; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_26);
x_36 = lean_unbox_uint32(x_30);
lean_dec(x_30);
lean_ctor_set_uint32(x_35, sizeof(void*)*2, x_36);
lean_ctor_set(x_32, 0, x_35);
return x_32;
}
else
{
lean_object* x_37; lean_object* x_38; uint32_t x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_32, 0);
lean_inc(x_37);
lean_dec(x_32);
x_38 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_26);
x_39 = lean_unbox_uint32(x_30);
lean_dec(x_30);
lean_ctor_set_uint32(x_38, sizeof(void*)*2, x_39);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_38);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_30);
lean_dec(x_26);
x_41 = !lean_is_exclusive(x_32);
if (x_41 == 0)
{
return x_32;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_32, 0);
lean_inc(x_42);
lean_dec(x_32);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
}
}
else
{
lean_object* x_49; uint32_t x_61; uint32_t x_62; uint8_t x_63; 
x_49 = lean_ctor_get(x_28, 0);
lean_inc(x_49);
lean_dec(x_28);
x_61 = 0;
x_62 = lean_unbox_uint32(x_49);
x_63 = lean_uint32_dec_eq(x_62, x_61);
if (x_63 == 0)
{
if (x_4 == 0)
{
goto block_60;
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_49);
lean_dec_ref(x_24);
x_64 = lean_mk_io_user_error(x_26);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
return x_65;
}
}
else
{
goto block_60;
}
block_60:
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_task_get_own(x_24);
x_51 = lp_batteries_IO_ofExcept___at___00IO_Process_runCmdWithInput_x27_spec__0___redArg(x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint32_t x_55; lean_object* x_56; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 x_53 = x_51;
} else {
 lean_dec_ref(x_51);
 x_53 = lean_box(0);
}
x_54 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_26);
x_55 = lean_unbox_uint32(x_49);
lean_dec(x_49);
lean_ctor_set_uint32(x_54, sizeof(void*)*2, x_55);
if (lean_is_scalar(x_53)) {
 x_56 = lean_alloc_ctor(0, 1, 0);
} else {
 x_56 = x_53;
}
lean_ctor_set(x_56, 0, x_54);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_49);
lean_dec(x_26);
x_57 = lean_ctor_get(x_51, 0);
lean_inc(x_57);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 x_58 = x_51;
} else {
 lean_dec_ref(x_51);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 1, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_57);
return x_59;
}
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_26);
lean_dec_ref(x_24);
x_66 = !lean_is_exclusive(x_28);
if (x_66 == 0)
{
return x_28;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_28, 0);
lean_inc(x_67);
lean_dec(x_28);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec_ref(x_24);
lean_dec(x_17);
x_69 = !lean_is_exclusive(x_25);
if (x_69 == 0)
{
return x_25;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_25, 0);
lean_inc(x_70);
lean_dec(x_25);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_17);
x_72 = !lean_is_exclusive(x_19);
if (x_72 == 0)
{
return x_19;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_19, 0);
lean_inc(x_73);
lean_dec(x_19);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_17);
lean_dec(x_16);
x_75 = !lean_is_exclusive(x_18);
if (x_75 == 0)
{
return x_18;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_18, 0);
lean_inc(x_76);
lean_dec(x_18);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
}
}
else
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_14);
if (x_78 == 0)
{
return x_14;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_14, 0);
lean_inc(x_79);
lean_dec(x_14);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
}
}
else
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_12);
if (x_81 == 0)
{
return x_12;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_12, 0);
lean_inc(x_82);
lean_dec(x_12);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_82);
return x_83;
}
}
}
}
LEAN_EXPORT lean_object* lp_batteries_IO_Process_runCmdWithInput_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
x_7 = lp_batteries_IO_Process_runCmdWithInput_x27(x_1, x_2, x_3, x_6);
lean_dec_ref(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_batteries_IO_Process_runCmdWithInput(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_6; 
x_6 = lp_batteries_IO_Process_runCmdWithInput_x27(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_9);
lean_dec(x_8);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_11);
lean_dec(x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_6, 0);
lean_inc(x_14);
lean_dec(x_6);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* lp_batteries_IO_Process_runCmdWithInput___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
x_7 = lp_batteries_IO_Process_runCmdWithInput(x_1, x_2, x_3, x_6);
lean_dec_ref(x_3);
return x_7;
}
}
lean_object* initialize_Init(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_batteries_Batteries_Lean_IO_Process(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_batteries_IO_Process_runCmdWithInput_x27___closed__0 = _init_lp_batteries_IO_Process_runCmdWithInput_x27___closed__0();
lean_mark_persistent(lp_batteries_IO_Process_runCmdWithInput_x27___closed__0);
lp_batteries_IO_Process_runCmdWithInput_x27___closed__1 = _init_lp_batteries_IO_Process_runCmdWithInput_x27___closed__1();
lean_mark_persistent(lp_batteries_IO_Process_runCmdWithInput_x27___closed__1);
lp_batteries_IO_Process_runCmdWithInput_x27___closed__2 = _init_lp_batteries_IO_Process_runCmdWithInput_x27___closed__2();
lean_mark_persistent(lp_batteries_IO_Process_runCmdWithInput_x27___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
