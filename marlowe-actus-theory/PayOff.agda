module POF where
  open import Utils
  _POF_PY_PAM_PYTP_A :
    Integer →
    Integer →
    Integer → Integer → Integer → Integer → Integer → Integer → Integer
  _POF_PY_PAM_PYTP_A o_rf_CURS o_rf_RRMO _PYRT _cPYRT _CNTRL nt ipnr
  y_sd_t
    = ( ( o_rf_CURS * (roleSign _CNTRL)) * _PYRT)
  _POF_PY_PAM_PYTP_N :
    Integer →
    Integer →
    Integer → Integer → Integer → Integer → Integer → Integer → Integer
  _POF_PY_PAM_PYTP_N o_rf_CURS o_rf_RRMO _PYRT _cPYRT _CNTRL nt ipnr
  y_sd_t
    = _cPYRT
  _POF_PY_PAM_PYTP_I :
    Integer →
    Integer →
    Integer → Integer → Integer → Integer → Integer → Integer → Integer
  _POF_PY_PAM_PYTP_I o_rf_CURS o_rf_RRMO _PYRT _cPYRT _CNTRL nt ipnr
  y_sd_t
    = ( ( ( ( o_rf_CURS * (roleSign _CNTRL)) * y_sd_t) * nt) *
       (max (+ 0) ( ipnr - o_rf_RRMO)))
  _POF_PY_PAM_PYTP_O :
    Integer →
    Integer →
    Integer → Integer → Integer → Integer → Integer → Integer → Integer
  _POF_PY_PAM_PYTP_O o_rf_CURS o_rf_RRMO _PYRT _cPYRT _CNTRL nt ipnr
  y_sd_t
    = (+ 0)