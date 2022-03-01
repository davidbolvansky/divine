// NOTE: Assertions have been autogenerated by utils/update_cc_test_checks.py
// REQUIRES: aarch64-registered-target
// RUN: %clang_cc1 -triple aarch64-none-linux-gnu -target-feature +sve -msve-vector-bits=512 -fallow-half-arguments-and-returns -fno-experimental-new-pass-manager -S -O1 -emit-llvm -o - %s | FileCheck %s

#include <arm_sve.h>

#define N __ARM_FEATURE_SVE_BITS

typedef svint32_t fixed_int32_t __attribute__((arm_sve_vector_bits(N)));
typedef svfloat64_t fixed_float64_t __attribute__((arm_sve_vector_bits(N)));
typedef svbool_t fixed_bool_t __attribute__((arm_sve_vector_bits(N)));

//===----------------------------------------------------------------------===//
// Test caller/callee with VLST <-> VLAT
//===----------------------------------------------------------------------===//

// CHECK-LABEL: @sizeless_callee(
// CHECK-NEXT:  entry:
// CHECK-NEXT:    ret <vscale x 4 x i32> [[X:%.*]]
//
svint32_t sizeless_callee(svint32_t x) {
  return x;
}

// CHECK-LABEL: @fixed_caller(
// CHECK-NEXT:  entry:
// CHECK-NEXT:    ret <vscale x 4 x i32> [[X_COERCE:%.*]]
//
fixed_int32_t fixed_caller(fixed_int32_t x) {
  return sizeless_callee(x);
}

// CHECK-LABEL: @fixed_callee(
// CHECK-NEXT:  entry:
// CHECK-NEXT:    ret <vscale x 4 x i32> [[X_COERCE:%.*]]
//
fixed_int32_t fixed_callee(fixed_int32_t x) {
  return x;
}

// CHECK-LABEL: @sizeless_caller(
// CHECK-NEXT:  entry:
// CHECK-NEXT:    [[COERCE1:%.*]] = alloca <16 x i32>, align 16
// CHECK-NEXT:    [[TMP0:%.*]] = bitcast <16 x i32>* [[COERCE1]] to <vscale x 4 x i32>*
// CHECK-NEXT:    store <vscale x 4 x i32> [[X:%.*]], <vscale x 4 x i32>* [[TMP0]], align 16
// CHECK-NEXT:    [[TMP1:%.*]] = load <16 x i32>, <16 x i32>* [[COERCE1]], align 16, !tbaa [[TBAA6:![0-9]+]]
// CHECK-NEXT:    [[CASTSCALABLESVE2:%.*]] = call <vscale x 4 x i32> @llvm.experimental.vector.insert.nxv4i32.v16i32(<vscale x 4 x i32> undef, <16 x i32> [[TMP1]], i64 0)
// CHECK-NEXT:    ret <vscale x 4 x i32> [[CASTSCALABLESVE2]]
//
svint32_t sizeless_caller(svint32_t x) {
  return fixed_callee(x);
}

//===----------------------------------------------------------------------===//
// fixed, fixed
//===----------------------------------------------------------------------===//

// CHECK-LABEL: @call_int32_ff(
// CHECK-NEXT:  entry:
// CHECK-NEXT:    [[TMP0:%.*]] = call <vscale x 4 x i1> @llvm.aarch64.sve.convert.from.svbool.nxv4i1(<vscale x 16 x i1> [[PG:%.*]])
// CHECK-NEXT:    [[TMP1:%.*]] = call <vscale x 4 x i32> @llvm.aarch64.sve.sel.nxv4i32(<vscale x 4 x i1> [[TMP0]], <vscale x 4 x i32> [[OP1_COERCE:%.*]], <vscale x 4 x i32> [[OP2_COERCE:%.*]])
// CHECK-NEXT:    ret <vscale x 4 x i32> [[TMP1]]
//
fixed_int32_t call_int32_ff(svbool_t pg, fixed_int32_t op1, fixed_int32_t op2) {
  return svsel(pg, op1, op2);
}

// CHECK-LABEL: @call_float64_ff(
// CHECK-NEXT:  entry:
// CHECK-NEXT:    [[TMP0:%.*]] = call <vscale x 2 x i1> @llvm.aarch64.sve.convert.from.svbool.nxv2i1(<vscale x 16 x i1> [[PG:%.*]])
// CHECK-NEXT:    [[TMP1:%.*]] = call <vscale x 2 x double> @llvm.aarch64.sve.sel.nxv2f64(<vscale x 2 x i1> [[TMP0]], <vscale x 2 x double> [[OP1_COERCE:%.*]], <vscale x 2 x double> [[OP2_COERCE:%.*]])
// CHECK-NEXT:    ret <vscale x 2 x double> [[TMP1]]
//
fixed_float64_t call_float64_ff(svbool_t pg, fixed_float64_t op1, fixed_float64_t op2) {
  return svsel(pg, op1, op2);
}

// CHECK-LABEL: @call_bool_ff(
// CHECK-NEXT:  entry:
// CHECK-NEXT:    [[OP1:%.*]] = alloca <8 x i8>, align 16
// CHECK-NEXT:    [[OP2:%.*]] = alloca <8 x i8>, align 16
// CHECK-NEXT:    [[SAVED_VALUE:%.*]] = alloca <8 x i8>, align 16
// CHECK-NEXT:    [[SAVED_VALUE3:%.*]] = alloca <8 x i8>, align 16
// CHECK-NEXT:    [[SAVED_VALUE5:%.*]] = alloca <vscale x 16 x i1>, align 16
// CHECK-NEXT:    [[RETVAL_COERCE:%.*]] = alloca <vscale x 16 x i1>, align 16
// CHECK-NEXT:    [[TMP0:%.*]] = bitcast <8 x i8>* [[OP1]] to <vscale x 16 x i1>*
// CHECK-NEXT:    store <vscale x 16 x i1> [[OP1_COERCE:%.*]], <vscale x 16 x i1>* [[TMP0]], align 16
// CHECK-NEXT:    [[OP11:%.*]] = load <8 x i8>, <8 x i8>* [[OP1]], align 16, !tbaa [[TBAA6]]
// CHECK-NEXT:    [[TMP1:%.*]] = bitcast <8 x i8>* [[OP2]] to <vscale x 16 x i1>*
// CHECK-NEXT:    store <vscale x 16 x i1> [[OP2_COERCE:%.*]], <vscale x 16 x i1>* [[TMP1]], align 16
// CHECK-NEXT:    [[OP22:%.*]] = load <8 x i8>, <8 x i8>* [[OP2]], align 16, !tbaa [[TBAA6]]
// CHECK-NEXT:    store <8 x i8> [[OP11]], <8 x i8>* [[SAVED_VALUE]], align 16, !tbaa [[TBAA6]]
// CHECK-NEXT:    [[CASTFIXEDSVE:%.*]] = bitcast <8 x i8>* [[SAVED_VALUE]] to <vscale x 16 x i1>*
// CHECK-NEXT:    [[TMP2:%.*]] = load <vscale x 16 x i1>, <vscale x 16 x i1>* [[CASTFIXEDSVE]], align 16, !tbaa [[TBAA6]]
// CHECK-NEXT:    store <8 x i8> [[OP22]], <8 x i8>* [[SAVED_VALUE3]], align 16, !tbaa [[TBAA6]]
// CHECK-NEXT:    [[CASTFIXEDSVE4:%.*]] = bitcast <8 x i8>* [[SAVED_VALUE3]] to <vscale x 16 x i1>*
// CHECK-NEXT:    [[TMP3:%.*]] = load <vscale x 16 x i1>, <vscale x 16 x i1>* [[CASTFIXEDSVE4]], align 16, !tbaa [[TBAA6]]
// CHECK-NEXT:    [[TMP4:%.*]] = call <vscale x 16 x i1> @llvm.aarch64.sve.sel.nxv16i1(<vscale x 16 x i1> [[PG:%.*]], <vscale x 16 x i1> [[TMP2]], <vscale x 16 x i1> [[TMP3]])
// CHECK-NEXT:    store <vscale x 16 x i1> [[TMP4]], <vscale x 16 x i1>* [[SAVED_VALUE5]], align 16, !tbaa [[TBAA9:![0-9]+]]
// CHECK-NEXT:    [[CASTFIXEDSVE6:%.*]] = bitcast <vscale x 16 x i1>* [[SAVED_VALUE5]] to <8 x i8>*
// CHECK-NEXT:    [[TMP5:%.*]] = load <8 x i8>, <8 x i8>* [[CASTFIXEDSVE6]], align 16, !tbaa [[TBAA6]]
// CHECK-NEXT:    [[RETVAL_0__SROA_CAST:%.*]] = bitcast <vscale x 16 x i1>* [[RETVAL_COERCE]] to <8 x i8>*
// CHECK-NEXT:    store <8 x i8> [[TMP5]], <8 x i8>* [[RETVAL_0__SROA_CAST]], align 16
// CHECK-NEXT:    [[TMP6:%.*]] = load <vscale x 16 x i1>, <vscale x 16 x i1>* [[RETVAL_COERCE]], align 16
// CHECK-NEXT:    ret <vscale x 16 x i1> [[TMP6]]
//
fixed_bool_t call_bool_ff(svbool_t pg, fixed_bool_t op1, fixed_bool_t op2) {
  return svsel(pg, op1, op2);
}

//===----------------------------------------------------------------------===//
// fixed, scalable
//===----------------------------------------------------------------------===//

// CHECK-LABEL: @call_int32_fs(
// CHECK-NEXT:  entry:
// CHECK-NEXT:    [[TMP0:%.*]] = call <vscale x 4 x i1> @llvm.aarch64.sve.convert.from.svbool.nxv4i1(<vscale x 16 x i1> [[PG:%.*]])
// CHECK-NEXT:    [[TMP1:%.*]] = call <vscale x 4 x i32> @llvm.aarch64.sve.sel.nxv4i32(<vscale x 4 x i1> [[TMP0]], <vscale x 4 x i32> [[OP1_COERCE:%.*]], <vscale x 4 x i32> [[OP2:%.*]])
// CHECK-NEXT:    ret <vscale x 4 x i32> [[TMP1]]
//
fixed_int32_t call_int32_fs(svbool_t pg, fixed_int32_t op1, svint32_t op2) {
  return svsel(pg, op1, op2);
}

// CHECK-LABEL: @call_float64_fs(
// CHECK-NEXT:  entry:
// CHECK-NEXT:    [[TMP0:%.*]] = call <vscale x 2 x i1> @llvm.aarch64.sve.convert.from.svbool.nxv2i1(<vscale x 16 x i1> [[PG:%.*]])
// CHECK-NEXT:    [[TMP1:%.*]] = call <vscale x 2 x double> @llvm.aarch64.sve.sel.nxv2f64(<vscale x 2 x i1> [[TMP0]], <vscale x 2 x double> [[OP1_COERCE:%.*]], <vscale x 2 x double> [[OP2:%.*]])
// CHECK-NEXT:    ret <vscale x 2 x double> [[TMP1]]
//
fixed_float64_t call_float64_fs(svbool_t pg, fixed_float64_t op1, svfloat64_t op2) {
  return svsel(pg, op1, op2);
}

// CHECK-LABEL: @call_bool_fs(
// CHECK-NEXT:  entry:
// CHECK-NEXT:    [[OP1:%.*]] = alloca <8 x i8>, align 16
// CHECK-NEXT:    [[SAVED_VALUE:%.*]] = alloca <8 x i8>, align 16
// CHECK-NEXT:    [[SAVED_VALUE2:%.*]] = alloca <vscale x 16 x i1>, align 16
// CHECK-NEXT:    [[RETVAL_COERCE:%.*]] = alloca <vscale x 16 x i1>, align 16
// CHECK-NEXT:    [[TMP0:%.*]] = bitcast <8 x i8>* [[OP1]] to <vscale x 16 x i1>*
// CHECK-NEXT:    store <vscale x 16 x i1> [[OP1_COERCE:%.*]], <vscale x 16 x i1>* [[TMP0]], align 16
// CHECK-NEXT:    [[OP11:%.*]] = load <8 x i8>, <8 x i8>* [[OP1]], align 16, !tbaa [[TBAA6]]
// CHECK-NEXT:    store <8 x i8> [[OP11]], <8 x i8>* [[SAVED_VALUE]], align 16, !tbaa [[TBAA6]]
// CHECK-NEXT:    [[CASTFIXEDSVE:%.*]] = bitcast <8 x i8>* [[SAVED_VALUE]] to <vscale x 16 x i1>*
// CHECK-NEXT:    [[TMP1:%.*]] = load <vscale x 16 x i1>, <vscale x 16 x i1>* [[CASTFIXEDSVE]], align 16, !tbaa [[TBAA6]]
// CHECK-NEXT:    [[TMP2:%.*]] = call <vscale x 16 x i1> @llvm.aarch64.sve.sel.nxv16i1(<vscale x 16 x i1> [[PG:%.*]], <vscale x 16 x i1> [[TMP1]], <vscale x 16 x i1> [[OP2:%.*]])
// CHECK-NEXT:    store <vscale x 16 x i1> [[TMP2]], <vscale x 16 x i1>* [[SAVED_VALUE2]], align 16, !tbaa [[TBAA9]]
// CHECK-NEXT:    [[CASTFIXEDSVE3:%.*]] = bitcast <vscale x 16 x i1>* [[SAVED_VALUE2]] to <8 x i8>*
// CHECK-NEXT:    [[TMP3:%.*]] = load <8 x i8>, <8 x i8>* [[CASTFIXEDSVE3]], align 16, !tbaa [[TBAA6]]
// CHECK-NEXT:    [[RETVAL_0__SROA_CAST:%.*]] = bitcast <vscale x 16 x i1>* [[RETVAL_COERCE]] to <8 x i8>*
// CHECK-NEXT:    store <8 x i8> [[TMP3]], <8 x i8>* [[RETVAL_0__SROA_CAST]], align 16
// CHECK-NEXT:    [[TMP4:%.*]] = load <vscale x 16 x i1>, <vscale x 16 x i1>* [[RETVAL_COERCE]], align 16
// CHECK-NEXT:    ret <vscale x 16 x i1> [[TMP4]]
//
fixed_bool_t call_bool_fs(svbool_t pg, fixed_bool_t op1, svbool_t op2) {
  return svsel(pg, op1, op2);
}

//===----------------------------------------------------------------------===//
// scalable, scalable
//===----------------------------------------------------------------------===//

// CHECK-LABEL: @call_int32_ss(
// CHECK-NEXT:  entry:
// CHECK-NEXT:    [[TMP0:%.*]] = call <vscale x 4 x i1> @llvm.aarch64.sve.convert.from.svbool.nxv4i1(<vscale x 16 x i1> [[PG:%.*]])
// CHECK-NEXT:    [[TMP1:%.*]] = call <vscale x 4 x i32> @llvm.aarch64.sve.sel.nxv4i32(<vscale x 4 x i1> [[TMP0]], <vscale x 4 x i32> [[OP1:%.*]], <vscale x 4 x i32> [[OP2:%.*]])
// CHECK-NEXT:    ret <vscale x 4 x i32> [[TMP1]]
//
fixed_int32_t call_int32_ss(svbool_t pg, svint32_t op1, svint32_t op2) {
  return svsel(pg, op1, op2);
}

// CHECK-LABEL: @call_float64_ss(
// CHECK-NEXT:  entry:
// CHECK-NEXT:    [[TMP0:%.*]] = call <vscale x 2 x i1> @llvm.aarch64.sve.convert.from.svbool.nxv2i1(<vscale x 16 x i1> [[PG:%.*]])
// CHECK-NEXT:    [[TMP1:%.*]] = call <vscale x 2 x double> @llvm.aarch64.sve.sel.nxv2f64(<vscale x 2 x i1> [[TMP0]], <vscale x 2 x double> [[OP1:%.*]], <vscale x 2 x double> [[OP2:%.*]])
// CHECK-NEXT:    ret <vscale x 2 x double> [[TMP1]]
//
fixed_float64_t call_float64_ss(svbool_t pg, svfloat64_t op1, svfloat64_t op2) {
  return svsel(pg, op1, op2);
}

// CHECK-LABEL: @call_bool_ss(
// CHECK-NEXT:  entry:
// CHECK-NEXT:    [[SAVED_VALUE:%.*]] = alloca <vscale x 16 x i1>, align 16
// CHECK-NEXT:    [[RETVAL_COERCE:%.*]] = alloca <vscale x 16 x i1>, align 16
// CHECK-NEXT:    [[TMP0:%.*]] = call <vscale x 16 x i1> @llvm.aarch64.sve.sel.nxv16i1(<vscale x 16 x i1> [[PG:%.*]], <vscale x 16 x i1> [[OP1:%.*]], <vscale x 16 x i1> [[OP2:%.*]])
// CHECK-NEXT:    store <vscale x 16 x i1> [[TMP0]], <vscale x 16 x i1>* [[SAVED_VALUE]], align 16, !tbaa [[TBAA9]]
// CHECK-NEXT:    [[CASTFIXEDSVE:%.*]] = bitcast <vscale x 16 x i1>* [[SAVED_VALUE]] to <8 x i8>*
// CHECK-NEXT:    [[TMP1:%.*]] = load <8 x i8>, <8 x i8>* [[CASTFIXEDSVE]], align 16, !tbaa [[TBAA6]]
// CHECK-NEXT:    [[RETVAL_0__SROA_CAST:%.*]] = bitcast <vscale x 16 x i1>* [[RETVAL_COERCE]] to <8 x i8>*
// CHECK-NEXT:    store <8 x i8> [[TMP1]], <8 x i8>* [[RETVAL_0__SROA_CAST]], align 16
// CHECK-NEXT:    [[TMP2:%.*]] = load <vscale x 16 x i1>, <vscale x 16 x i1>* [[RETVAL_COERCE]], align 16
// CHECK-NEXT:    ret <vscale x 16 x i1> [[TMP2]]
//
fixed_bool_t call_bool_ss(svbool_t pg, svbool_t op1, svbool_t op2) {
  return svsel(pg, op1, op2);
}
