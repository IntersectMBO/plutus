#ifndef _hs_double_conversion_h
#define _hs_double_conversion_h

#ifdef __cplusplus
extern "C"
{
#endif

#include <stddef.h>

int _hs_ToShortestLength(void);
int _hs_Text_ToShortest(double value, uint16_t *buf);
int _hs_ToShortest(double value, char *buf);
int _hs_ToFixedLength(void);
int _hs_Text_ToFixed(double value, uint16_t *buf, int ndigits);
int _hs_ToFixed(double value, char *buf, int ndigits);
int _hs_ToExponentialLength(void);
int _hs_Text_ToExponential(double value, uint16_t *buf, int ndigits);
int _hs_ToExponential(double value, char *buf, int ndigits);
int _hs_ToPrecisionLength(void);
int _hs_Text_ToPrecision(double value, uint16_t *buf, int ndigits);
int _hs_ToPrecision(double value, char *buf, int ndigits);

#ifdef __cplusplus
}
#endif

#endif /* _hs_double_conversion_h */
