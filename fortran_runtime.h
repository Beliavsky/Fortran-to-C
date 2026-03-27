#ifndef FORTRAN_RUNTIME_H
#define FORTRAN_RUNTIME_H

#include <stdint.h>

int len_trim_s(const char *s); /* Return the length after removing trailing blanks. */
const char *trim_s(const char *s); /* Copy the string without trailing blanks. */
const char *adjustl_s(const char *s); /* Shift leading blanks to the end, preserving total length. */
const char *concat_s2(const char *a, const char *b); /* Concatenate two CHARACTER values into a temporary buffer. */
const char *adjustr_s(const char *s); /* Shift trailing blanks to the front, preserving total length. */
const char *repeat_s(const char *s, int ncopy); /* Concatenate the same source string ncopy times. */
const char *substr_s(const char *s, int lo, int hi); /* Extract a 1-based inclusive substring with Fortran bounds clipping. */
char *copy_str_s(const char *s); /* Make a stable heap copy of a string expression result. */
int index_s(const char *s, const char *sub); /* Return the 1-based position of the first matching substring. */
void assign_str(char *dst, int len, const char *src); /* Assign into a fixed-length CHARACTER target with blank padding. */
void assign_substr(char *dst, int len, int lo, int hi, const char *src); /* Assign into a fixed-length substring slice using Fortran bounds rules. */
void assign_str_alloc(char **dst, const char *src); /* Replace a heap-backed CHARACTER element with a duplicated C string. */
void free_str_array(char **arr, int n); /* Free each heap-backed CHARACTER element and then its pointer array. */
int scan_s(const char *s, const char *set); /* Return the 1-based location of the first character found in set. */
int verify_s(const char *s, const char *set); /* Return the 1-based location of the first character not in set. */
const char *achar_s(int code); /* Build a one-character string from an integer code. */
int iachar_s(const char *s); /* Return the code of the first character, or zero for empty input. */

int open_unit(int unit, const char *file, const char *action, const char *status); /* Open a file and bind it to a simple logical-unit table entry. */
int close_unit(int unit); /* Close the file currently associated with a logical unit number. */
int rewind_unit(int unit); /* Reposition an open logical unit to the beginning of the file. */
int backspace_unit(int unit); /* Reposition an open logical unit to the start of the previous record. */
int alloc_unit(void); /* Pick the first unused logical unit number in a simple fixed table. */
int write_bytes_unit(int unit, long pos1, const void *buf, size_t elem_size, int count); /* Write raw stream bytes at the current position or a 1-based stream POS. */
int read_bytes_unit(int unit, long pos1, void *buf, size_t elem_size, int count); /* Read raw stream bytes at the current position or a 1-based stream POS. */
void write_a(int unit, const char *s); /* Write one character record with a trailing newline. */
void write_i0_then_words(int unit, int iv, int n, const char *const *words); /* Write i0 followed by n space-separated character items. */
int write_int_float_record(int unit, int iw, int fw, int fd, int iv, double rv); /* Write one formatted INTEGER/REAL text record. */
int read_a(int unit, char *buf, int len); /* Read one character record and blank-pad the destination buffer. */
int read_int_float_record(int unit, int *iv, float *rv); /* Read one whitespace-separated INTEGER/REAL text record. */
int read_int_double_record(int unit, int *iv, double *rv); /* Read one whitespace-separated INTEGER/DOUBLE text record. */
int read_int_s(const char *s, int *out); /* Parse a scalar INTEGER from an internal character buffer. */
int read_float_s(const char *s, float *out); /* Parse a scalar REAL from an internal character buffer. */
int read_double_s(const char *s, double *out); /* Parse a scalar DOUBLE PRECISION value from an internal character buffer. */
int read_first_int_s(const char *s, int *out); /* Parse the leading INTEGER item from an internal list-directed record. */
int read_first_float_s(const char *s, float *out); /* Parse the leading REAL item from an internal list-directed record. */
int read_first_double_s(const char *s, double *out); /* Parse the leading DOUBLE PRECISION item from an internal list-directed record. */
int read_words_after_int_s(const char *s, int nw, char **words); /* Parse an initial count followed by whitespace-delimited words. */
int count_fields(const char *line); /* Count comma-separated fields in a trimmed input line. */
void split_csv_line(const char *line, int n, char **fields); /* Split a trimmed CSV line on commas into a fixed output field array. */
void fill_rand_1d_float(int n, float *x); /* Fill a 1D REAL array with uniform pseudo-random values in [0, 1]. */
void fill_rand_1d_double(int n, double *x); /* Fill a 1D DOUBLE PRECISION array with uniform pseudo-random values in [0, 1]. */
void rng_seed(int64_t seed); /* Seed the shared MT19937-64 generator with one integer seed. */
double runif(void); /* Return one reproducible uniform variate in [0, 1). */
void fill_runif_1d(int n, double *x); /* Fill a 1D DOUBLE PRECISION array with reproducible MT19937-64 uniforms. */
void fill_runif_2d(int n1, int n2, double *x); /* Fill a 2D DOUBLE PRECISION array with reproducible MT19937-64 uniforms. */

float sum_1d_float(int n, const float *x); /* Sum all elements of a 1D REAL array. */
double sum_1d_double(int n, const double *x); /* Sum all elements of a 1D DOUBLE PRECISION array. */
int sum_1d_int(int n, const int *x); /* Sum all elements of a 1D INTEGER array. */
float product_1d_float(int n, const float *x); /* Multiply all elements of a 1D REAL array. */
double product_1d_double(int n, const double *x); /* Multiply all elements of a 1D DOUBLE PRECISION array. */
float minval_1d_float(int n, const float *x); /* Return the smallest element of a 1D REAL array. */
double minval_1d_double(int n, const double *x); /* Return the smallest element of a 1D DOUBLE PRECISION array. */
int minval_1d_int(int n, const int *x); /* Return the smallest element of a 1D INTEGER array. */
float maxval_1d_float(int n, const float *x); /* Return the largest element of a 1D REAL array. */
double maxval_1d_double(int n, const double *x); /* Return the largest element of a 1D DOUBLE PRECISION array. */
int maxval_1d_int(int n, const int *x); /* Return the largest element of a 1D INTEGER array. */
int count_1d_int(int n, const int *x); /* Count nonzero elements of a 1D LOGICAL/INTEGER mask array. */
int any_1d_int(int n, const int *x); /* Return whether any element of a 1D LOGICAL/INTEGER mask is true. */
int all_1d_int(int n, const int *x); /* Return whether every element of a 1D LOGICAL/INTEGER mask is true. */
float dot_product_1d_float(int n, const float *x, const float *y); /* Compute the dot product of two 1D REAL arrays. */
double dot_product_1d_double(int n, const double *x, const double *y); /* Compute the dot product of two 1D DOUBLE PRECISION arrays. */
int dot_product_1d_int(int n, const int *x, const int *y); /* Compute the dot product of two 1D INTEGER arrays. */

#endif
