#include "blst.h"
#include <memory.h>

const size_t size_blst_p1 () { return sizeof(blst_p1); }
const size_t size_blst_p2 () { return sizeof(blst_p2); }
const size_t size_blst_scalar () { return sizeof(blst_scalar); }
const size_t size_blst_fr () { return sizeof(blst_fr); }
const size_t size_blst_fp12 () { return sizeof(blst_fp12); }
const size_t size_blst_affine1 () { return sizeof(blst_p1_affine); }
const size_t size_blst_affine2 () { return sizeof(blst_p2_affine); }

const int blst_success () { return BLST_SUCCESS; }
const int blst_error_bad_encoding () { return BLST_BAD_ENCODING; }
const int blst_error_point_not_on_curve () { return BLST_POINT_NOT_ON_CURVE; }
const int blst_error_point_not_in_group () { return BLST_POINT_NOT_IN_GROUP; }
const int blst_error_aggr_type_mismatch () { return BLST_AGGR_TYPE_MISMATCH; }
const int blst_error_verify_fail () { return BLST_VERIFY_FAIL; }
const int blst_error_pk_is_infinity () { return BLST_PK_IS_INFINITY; }
const int blst_error_bad_scalar () { return BLST_BAD_SCALAR; }
