#include "fortran_runtime.h"

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <ctype.h>

static char *tmp_str_buf(size_t need) {
   /* Reuse a small ring of heap buffers for transient string results. */
   static char *buf[8] = {0};
   static size_t cap[8] = {0};
   static int slot = 0;
   int use = slot;
   char *out;
   slot = (slot + 1) % 8;
   if (need + 1u > cap[use]) {
      char *tmp = (char *) realloc(buf[use], need + 1u);
      if (!tmp) {
         fprintf(stderr, "tmp_str_buf: out of memory\n");
         exit(1);
      }
      buf[use] = tmp;
      cap[use] = need + 1u;
   }
   out = buf[use];
   out[0] = '\0';
   return out;
}


int len_trim_s(const char *s) {
   /* Return the length after removing trailing blanks. */
   int n = (int) strlen(s);
   while (n > 0 && s[n - 1] == ' ') --n;
   return n;
}


const char *trim_s(const char *s) {
   /* Copy the string without trailing blanks. */
   if (!s) return tmp_str_buf(0);
   int n = len_trim_s(s);
   char *out = tmp_str_buf((size_t) n);
   memcpy(out, s, (size_t) n);
   out[n] = '\0';
   return out;
}


const char *adjustl_s(const char *s) {
   /* Shift leading blanks to the end, preserving total length. */
   if (!s) return tmp_str_buf(0);
   int n = (int) strlen(s);
   char *out = tmp_str_buf((size_t) n);
   int i = 0;
   while (i < n && s[i] == ' ') ++i;
   int m = n - i;
   if (m > 0) memcpy(out, s + i, (size_t) m);
   for (int k = m; k < n; ++k) out[k] = ' ';
   out[n] = '\0';
   return out;
}


const char *concat_s2(const char *a, const char *b) {
   /* Concatenate two CHARACTER values into a reusable temporary buffer. */
   int na = a ? (int) strlen(a) : 0;
   int nb = b ? (int) strlen(b) : 0;
   char *out = tmp_str_buf((size_t) (na + nb));
   if (na > 0) memcpy(out, a, (size_t) na);
   if (nb > 0) memcpy(out + na, b, (size_t) nb);
   out[na + nb] = '\0';
   return out;
}


const char *adjustr_s(const char *s) {
   /* Shift trailing blanks to the front, preserving total length. */
   if (!s) return tmp_str_buf(0);
   int n = (int) strlen(s);
   int m = len_trim_s(s);
   char *out = tmp_str_buf((size_t) n);
   if (m > n) m = n;
   for (int k = 0; k < n - m; ++k) out[k] = ' ';
   if (m > 0) memcpy(out + (n - m), s, (size_t) m);
   out[n] = '\0';
   return out;
}


const char *repeat_s(const char *s, int ncopy) {
   /* Concatenate the same source string ncopy times. */
   if (!s || ncopy <= 0) return tmp_str_buf(0);
   size_t used = 0;
   size_t m = strlen(s);
   size_t copies = (size_t) ncopy;
   size_t need = (m > 0u && copies > ((((size_t)-1) - 1u) / m)) ? (((size_t)-1) - 1u) : (m * copies);
   char *out = tmp_str_buf(need);
   for (int i = 0; i < ncopy; ++i) {
      if (m > 0u) memcpy(out + used, s, m);
      used += m;
   }
   out[used] = '\0';
   return out;
}


const char *substr_s(const char *s, int lo, int hi) {
   /* Extract a 1-based inclusive substring with Fortran bounds clipping. */
   if (!s) return tmp_str_buf(0);
   int n = (int) strlen(s);
   if (lo < 1) lo = 1;
   if (hi > n) hi = n;
   if (hi < lo) return tmp_str_buf(0);
   int m = hi - lo + 1;
   char *out = tmp_str_buf((size_t) m);
   memcpy(out, s + (lo - 1), (size_t) m);
   out[m] = '\0';
   return out;
}


char *copy_str_s(const char *s) {
   /* Make a stable heap copy of a string expression result. */
   const char *src = s ? s : "";
   size_t n = strlen(src);
   char *out = (char *) malloc(n + 1u);
   if (!out) return NULL;
   if (n > 0) memcpy(out, src, n);
   out[n] = '\0';
   return out;
}


int index_s(const char *s, const char *sub) {
   /* Return the 1-based position of the first matching substring. */
   const char *p = strstr(s, sub);
   return p ? (int) (p - s) + 1 : 0;
}


void assign_str(char *dst, int len, const char *src) {
   /* Assign into a fixed-length CHARACTER target with blank padding. */
   if (!dst || len < 0) return;
   const char *src_use = src;
   char *tmp = NULL;
   int n = 0;
   if (src_use) {
      n = (int) strlen(src_use);
      if (n > len) n = len;
      if (src_use >= dst && src_use <= dst + len) {
         tmp = (char *) malloc((size_t) n + 1u);
         if (tmp) {
            if (n > 0) memcpy(tmp, src_use, (size_t) n);
            tmp[n] = '\0';
            src_use = tmp;
         }
      }
   }
   for (int i = 0; i < len; ++i) dst[i] = ' ';
   if (src_use && n > 0) memcpy(dst, src_use, (size_t) n);
   dst[len] = '\0';
   if (tmp) free(tmp);
}


void assign_substr(char *dst, int len, int lo, int hi, const char *src) {
   /* Assign into a fixed-length substring slice using Fortran bounds rules. */
   if (!dst || len < 0) return;
   if (lo < 1) lo = 1;
   if (hi > len) hi = len;
   if (hi < lo) return;
   int span = hi - lo + 1;
   int n = src ? (int) strlen(src) : 0;
   if (n > span) n = span;
   if (n > 0) memmove(dst + (lo - 1), src, (size_t) n);
   for (int i = lo - 1 + n; i <= hi - 1; ++i) dst[i] = ' ';
   dst[len] = '\0';
}


void assign_str_alloc(char **dst, const char *src) {
   /* Replace a heap-backed CHARACTER element with a duplicated C string. */
   char *copy = NULL;
   const char *src_use = src ? src : "";
   size_t n = strlen(src_use);
   copy = (char *) malloc(n + 1u);
   if (!copy) return;
   if (n > 0) memcpy(copy, src_use, n);
   copy[n] = '\0';
   if (dst && *dst) free(*dst);
   if (dst) *dst = copy;
   else free(copy);
}


void free_str_array(char **arr, int n) {
   /* Free each heap-backed CHARACTER element and then its pointer array. */
   if (!arr) return;
   for (int i = 0; i < n; ++i) {
      if (arr[i]) free(arr[i]);
   }
   free(arr);
}


int scan_s(const char *s, const char *set) {
   /* Return the 1-based location of the first character found in set. */
   if (!s || !set) return 0;
   for (int i = 0; s[i] != '\0'; ++i) {
      if (strchr(set, s[i])) return i + 1;
   }
   return 0;
}


int verify_s(const char *s, const char *set) {
   /* Return the 1-based location of the first character not in set. */
   if (!s || !set) return 0;
   for (int i = 0; s[i] != '\0'; ++i) {
      if (!strchr(set, s[i])) return i + 1;
   }
   return 0;
}


const char *achar_s(int code) {
   /* Build a one-character string from an integer code. */
   char *out = tmp_str_buf(1u);
   out[0] = (char) (unsigned char) code;
   out[1] = '\0';
   return out;
}


int iachar_s(const char *s) {
   /* Return the code of the first character, or zero for empty input. */
   return (s && s[0] != '\0') ? (int) ((unsigned char) s[0]) : 0;
}


static FILE *unit_files[1000] = {0};


static FILE *unit_get(int unit) {
   /* Look up the FILE* currently associated with a logical unit number. */
   if (unit >= 0 && unit < 1000) return unit_files[unit];
   return NULL;
}


int alloc_unit(void) {
   /* Pick the first unused logical unit number in a simple fixed table. */
   for (int unit = 10; unit < 1000; ++unit) {
      if (!unit_files[unit]) return unit;
   }
   return -1;
}


int open_unit(int unit, const char *file, const char *action, const char *status) {
   /* Open a file and bind it to a simple logical-unit table entry. */
   const char *mode = "r";
   if (action && strcmp(action, "write") == 0) mode = "w";
   else if (action && strcmp(action, "read") == 0) mode = "r";
   else if (action && strcmp(action, "readwrite") == 0) mode = "w+b";
   else if (status && strcmp(status, "replace") == 0) mode = "w";
   FILE *fp = fopen(file, mode);
   if (!fp) return 1;
   if (unit >= 0 && unit < 1000) unit_files[unit] = fp;
   return 0;
}


int close_unit(int unit) {
   /* Close the file currently associated with a logical unit number. */
   FILE *fp = unit_get(unit);
   if (!fp) return 1;
   fclose(fp);
   if (unit >= 0 && unit < 1000) unit_files[unit] = NULL;
   return 0;
}


int rewind_unit(int unit) {
   /* Reposition an open logical unit to the beginning of the file. */
   FILE *fp = unit_get(unit);
   if (!fp) return 1;
   return fseek(fp, 0L, SEEK_SET) == 0 ? 0 : 1;
}


int backspace_unit(int unit) {
   /* Reposition an open logical unit to the start of the previous text record. */
   FILE *fp = unit_get(unit);
   long pos;
   if (!fp) return 1;
   pos = ftell(fp);
   if (pos < 0) return 1;
   if (pos == 0) return 0;
   while (pos > 0) {
      int ch;
      --pos;
      if (fseek(fp, pos, SEEK_SET) != 0) return 1;
      ch = fgetc(fp);
      if (ch == '\n' || ch == '\r') continue;
      break;
   }
   while (pos > 0) {
      int ch;
      --pos;
      if (fseek(fp, pos, SEEK_SET) != 0) return 1;
      ch = fgetc(fp);
      if (ch == '\n' || ch == '\r') {
         ++pos;
         break;
      }
   }
   return fseek(fp, pos, SEEK_SET) == 0 ? 0 : 1;
}


int write_bytes_unit(int unit, long pos1, const void *buf, size_t elem_size, int count) {
   /* Write raw stream bytes at the current file position or a 1-based stream POS. */
   FILE *fp = unit_get(unit);
   if (!fp || (!buf && count > 0) || elem_size == 0 || count < 0) return 1;
   if (pos1 > 0 && fseek(fp, pos1 - 1, SEEK_SET) != 0) return 1;
   return fwrite(buf, elem_size, (size_t) count, fp) == (size_t) count ? 0 : 1;
}


int read_bytes_unit(int unit, long pos1, void *buf, size_t elem_size, int count) {
   /* Read raw stream bytes at the current file position or a 1-based stream POS. */
   FILE *fp = unit_get(unit);
   if (!fp || (!buf && count > 0) || elem_size == 0 || count < 0) return 1;
   if (pos1 > 0 && fseek(fp, pos1 - 1, SEEK_SET) != 0) return 1;
   return fread(buf, elem_size, (size_t) count, fp) == (size_t) count ? 0 : 1;
}


void write_a(int unit, const char *s) {
   /* Write one character record with a trailing newline. */
   FILE *fp = unit_get(unit);
   if (!fp) return;
   fprintf(fp, "%s\n", s ? s : "");
}


void write_i0_then_words(int unit, int iv, int n, const char *const *words) {
   /* Write i0 followed by n space-separated character items and a newline. */
   FILE *fp = unit_get(unit);
   if (!fp || (n > 0 && !words)) return;
   fprintf(fp, "%d", iv);
   for (int i = 0; i < n; ++i) {
      fprintf(fp, " %s", words[i] ? words[i] : "");
   }
   fputc('\n', fp);
}


int write_int_float_record(int unit, int iw, int fw, int fd, int iv, double rv) {
   /* Write one formatted INTEGER/REAL text record with explicit field widths. */
   FILE *fp = unit_get(unit);
   if (!fp) return 1;
   return fprintf(fp, "%*d %*.*f\n", iw, iv, fw, fd, rv) < 0 ? 1 : 0;
}


int read_a(int unit, char *buf, int len) {
   /* Read one character record and blank-pad the destination buffer. */
   FILE *fp = unit_get(unit);
   if (!fp || !buf || len < 0) return 1;
   for (int i = 0; i < len; ++i) buf[i] = ' ';
   buf[len] = '\0';
   if (!fgets(buf, len + 1, fp)) return 1;
   int n = (int) strlen(buf);
   while (n > 0 && (buf[n - 1] == '\n' || buf[n - 1] == '\r')) buf[--n] = '\0';
   for (int i = n; i < len; ++i) buf[i] = ' ';
   buf[len] = '\0';
   return 0;
}


int read_int_float_record(int unit, int *iv, float *rv) {
   /* Read one whitespace-separated INTEGER/REAL text record. */
   char buf[256];
   int itmp;
   float rtmp;
   FILE *fp = unit_get(unit);
   if (!fp || !iv || !rv) return 1;
   if (!fgets(buf, (int) sizeof(buf), fp)) return 1;
   if (sscanf(buf, "%d%f", &itmp, &rtmp) != 2) return 1;
   *iv = itmp;
   *rv = rtmp;
   return 0;
}


int read_int_double_record(int unit, int *iv, double *rv) {
   /* Read one whitespace-separated INTEGER/DOUBLE text record. */
   char buf[256];
   int itmp;
   double rtmp;
   FILE *fp = unit_get(unit);
   if (!fp || !iv || !rv) return 1;
   if (!fgets(buf, (int) sizeof(buf), fp)) return 1;
   if (sscanf(buf, "%d%lf", &itmp, &rtmp) != 2) return 1;
   *iv = itmp;
   *rv = rtmp;
   return 0;
}


static const char *skip_space_s(const char *s) {
   /* Advance past leading ASCII whitespace for internal reads. */
   while (s && *s != '\0' && (*s == ' ' || *s == '\t' || *s == '\r' || *s == '\n' || *s == '\f' || *s == '\v')) {
      ++s;
   }
   return s;
}


int read_int_s(const char *s, int *out) {
   /* Parse a scalar INTEGER from an internal character buffer. */
   char *end = NULL;
   long v;
   const char *src = skip_space_s(s);
   if (!src || !out || *src == '\0') return 1;
   v = strtol(src, &end, 10);
   if (end == src) return 1;
   end = (char *) skip_space_s(end);
   if (*end != '\0') return 1;
   *out = (int) v;
   return 0;
}


int read_first_int_s(const char *s, int *out) {
   /* Parse the leading INTEGER item from an internal list-directed record. */
   char *end = NULL;
   long v;
   const char *src = skip_space_s(s);
   if (!src || !out || *src == '\0') return 1;
   v = strtol(src, &end, 10);
   if (end == src) return 1;
   *out = (int) v;
   return 0;
}


int read_float_s(const char *s, float *out) {
   /* Parse a scalar REAL from an internal character buffer. */
   char *end = NULL;
   float v;
   const char *src = skip_space_s(s);
   if (!src || !out || *src == '\0') return 1;
   v = strtof(src, &end);
   if (end == src) return 1;
   end = (char *) skip_space_s(end);
   if (*end != '\0') return 1;
   *out = v;
   return 0;
}


int read_first_float_s(const char *s, float *out) {
   /* Parse the leading REAL item from an internal list-directed record. */
   char *end = NULL;
   float v;
   const char *src = skip_space_s(s);
   if (!src || !out || *src == '\0') return 1;
   v = strtof(src, &end);
   if (end == src) return 1;
   *out = v;
   return 0;
}


int read_double_s(const char *s, double *out) {
   /* Parse a scalar DOUBLE PRECISION value from an internal character buffer. */
   char *end = NULL;
   double v;
   const char *src = skip_space_s(s);
   if (!src || !out || *src == '\0') return 1;
   v = strtod(src, &end);
   if (end == src) return 1;
   end = (char *) skip_space_s(end);
   if (*end != '\0') return 1;
   *out = v;
   return 0;
}


int read_first_double_s(const char *s, double *out) {
   /* Parse the leading DOUBLE PRECISION item from an internal list-directed record. */
   char *end = NULL;
   double v;
   const char *src = skip_space_s(s);
   if (!src || !out || *src == '\0') return 1;
   v = strtod(src, &end);
   if (end == src) return 1;
   *out = v;
   return 0;
}


int read_words_after_int_s(const char *s, int nw, char **words) {
   /* Parse an initial count followed by nw whitespace-delimited words. */
   char *end = NULL;
   long v;
   const char *src = skip_space_s(s);
   if (!src || nw < 0 || (nw > 0 && !words) || *src == '\0') return 1;
   v = strtol(src, &end, 10);
   if (end == src || (int) v != nw) return 1;
   src = end;
   for (int i = 0; i < nw; ++i) {
      const char *start = NULL;
      size_t len = 0;
      src = skip_space_s(src);
      if (!src || *src == '\0') return 1;
      start = src;
      while (*src != '\0' && !isspace((unsigned char) *src)) ++src;
      len = (size_t) (src - start);
      if (len == 0) return 1;
      if (words[i]) free(words[i]);
      words[i] = (char *) malloc(len + 1);
      if (!words[i]) return 1;
      memcpy(words[i], start, len);
      words[i][len] = '\0';
   }
   src = skip_space_s(src);
   return (src && *src == '\0') ? 0 : 1;
}


int count_fields(const char *line) {
   /* Count comma-separated fields in a trimmed input line. */
   int nfields = 1;
   int lt = len_trim_s(line);
   for (int i = 1; i <= lt; ++i) {
      if (strcmp(substr_s(line, i, i), ",") == 0) ++nfields;
   }
   return nfields;
}


void split_csv_line(const char *line, int n, char **fields) {
   /* Split a trimmed CSV line on commas into a fixed output field array. */
   int lt = len_trim_s(line);
   int i0 = 1;
   int k = 1;
   for (int i_fill = 0; i_fill < n; ++i_fill) {
      assign_str_alloc(&fields[i_fill], "");
   }
   for (int i = 1; i <= lt; ++i) {
      if (strcmp(substr_s(line, i, i), ",") == 0) {
         if (k <= n) assign_str_alloc(&fields[k - 1], adjustl_s(substr_s(line, i0, i - 1)));
         ++k;
         i0 = i + 1;
      }
   }
   if (k <= n) assign_str_alloc(&fields[k - 1], adjustl_s(substr_s(line, i0, lt)));
}


void fill_rand_1d_float(int n, float *x) {
   /* Fill a 1D REAL array with uniform pseudo-random values in [0, 1]. */
   for (int i = 0; i < n; ++i) x[i] = (float) rand() / (float) RAND_MAX;
}


void fill_rand_1d_double(int n, double *x) {
   /* Fill a 1D DOUBLE PRECISION array with uniform pseudo-random values in [0, 1]. */
   for (int i = 0; i < n; ++i) x[i] = (double) rand() / (double) RAND_MAX;
}


static uint64_t mt_state[312] = {0};
static int mt_index = 313;
static void mt_seed_default(void);

void rng_seed(int64_t seed) {
   /* Seed the shared MT19937-64 generator with one integer seed. */
   mt_state[0] = (uint64_t) seed;
   for (mt_index = 1; mt_index < 312; ++mt_index) {
      mt_state[mt_index] = UINT64_C(6364136223846793005) *
                           (mt_state[mt_index - 1] ^ (mt_state[mt_index - 1] >> 62)) +
                           (uint64_t) mt_index;
   }
}


void rng_seed_vector(int n, const int64_t *seed) {
   /* Seed the shared MT19937-64 generator from an integer seed vector. */
   static const uint64_t c1 = UINT64_C(3935559000370003845);
   static const uint64_t c2 = UINT64_C(2862933555777941757);
   int i;
   int j;
   int k;
   int kk;

   if (!seed || n <= 0) {
      mt_seed_default();
      return;
   }

   rng_seed((int64_t) 19650218);
   i = 1;
   j = 0;
   k = (312 > n) ? 312 : n;

   for (kk = 0; kk < k; ++kk) {
      mt_state[i] = (mt_state[i] ^
                     (c1 * (mt_state[i - 1] ^ (mt_state[i - 1] >> 62)))) +
                    (uint64_t) seed[j] + (uint64_t) j;
      ++i;
      ++j;
      if (i >= 312) {
         mt_state[0] = mt_state[311];
         i = 1;
      }
      if (j >= n) j = 0;
   }

   for (kk = 0; kk < 311; ++kk) {
      mt_state[i] = (mt_state[i] ^
                     (c2 * (mt_state[i - 1] ^ (mt_state[i - 1] >> 62)))) -
                    (uint64_t) i;
      ++i;
      if (i >= 312) {
         mt_state[0] = mt_state[311];
         i = 1;
      }
   }

   mt_state[0] = UINT64_C(1) << 63;
   mt_index = 312;
}


static void mt_seed_default(void) {
   /* Seed the shared MT19937-64 generator with the original default seed. */
   rng_seed((int64_t) 5489);
}


static uint64_t mt_genrand64_int64(void) {
   /* Generate one 64-bit MT19937 output word. */
   static const uint64_t matrix_a = UINT64_C(0xB5026F5AA96619E9);
   static const uint64_t um = UINT64_C(0xFFFFFFFF80000000);
   static const uint64_t lm = UINT64_C(0x7FFFFFFF);
   static const uint64_t mag01[2] = {UINT64_C(0), matrix_a};
   uint64_t x;
   int i;

   if (mt_index >= 312) {
      if (mt_index == 313) mt_seed_default();

      for (i = 0; i < 312 - 156; ++i) {
         x = (mt_state[i] & um) | (mt_state[i + 1] & lm);
         mt_state[i] = mt_state[i + 156] ^ (x >> 1) ^ mag01[(int) (x & UINT64_C(1))];
      }
      for (; i < 311; ++i) {
         x = (mt_state[i] & um) | (mt_state[i + 1] & lm);
         mt_state[i] = mt_state[i + (156 - 312)] ^ (x >> 1) ^ mag01[(int) (x & UINT64_C(1))];
      }
      x = (mt_state[311] & um) | (mt_state[0] & lm);
      mt_state[311] = mt_state[155] ^ (x >> 1) ^ mag01[(int) (x & UINT64_C(1))];

      mt_index = 0;
   }

   x = mt_state[mt_index++];
   x ^= (x >> 29) & UINT64_C(0x5555555555555555);
   x ^= (x << 17) & UINT64_C(0x71D67FFFEDA60000);
   x ^= (x << 37) & UINT64_C(0xFFF7EEE000000000);
   x ^= (x >> 43);
   return x;
}


double runif(void) {
   /* Return one reproducible uniform variate in [0, 1). */
   return (double) (mt_genrand64_int64() >> 11) * (1.0 / 9007199254740992.0);
}


double *runif_1d(int n) {
   /* Allocate and return a 1D DOUBLE PRECISION array of reproducible MT19937-64 uniforms. */
   double *x;
   int i;

   if (n <= 0) return NULL;
   x = (double *) malloc(sizeof(double) * (size_t) n);
   if (!x) return NULL;
   for (i = 0; i < n; ++i) x[i] = runif();
   return x;
}


void fill_runif_1d(int n, double *x) {
   /* Fill a 1D DOUBLE PRECISION array with reproducible MT19937-64 uniforms. */
   for (int i = 0; i < n; ++i) x[i] = runif();
}


void fill_runif_2d(int n1, int n2, double *x) {
   /* Fill a 2D DOUBLE PRECISION array with reproducible MT19937-64 uniforms. */
   for (int j = 0; j < n2; ++j) {
      for (int i = 0; i < n1; ++i) {
         x[i + n1 * j] = runif();
      }
   }
}


float sum_1d_float(int n, const float *x) {
   /* Sum all elements of a 1D REAL array. */
   float s = 0.0f;
   for (int i = 0; i < n; ++i) s += x[i];
   return s;
}


double sum_1d_double(int n, const double *x) {
   /* Sum all elements of a 1D DOUBLE PRECISION array. */
   double s = 0.0;
   for (int i = 0; i < n; ++i) s += x[i];
   return s;
}


int sum_1d_int(int n, const int *x) {
   /* Sum all elements of a 1D INTEGER array. */
   int s = 0;
   for (int i = 0; i < n; ++i) s += x[i];
   return s;
}


float product_1d_float(int n, const float *x) {
   /* Multiply all elements of a 1D REAL array. */
   float p = 1.0f;
   for (int i = 0; i < n; ++i) p *= x[i];
   return p;
}


double product_1d_double(int n, const double *x) {
   /* Multiply all elements of a 1D DOUBLE PRECISION array. */
   double p = 1.0;
   for (int i = 0; i < n; ++i) p *= x[i];
   return p;
}


float minval_1d_float(int n, const float *x) {
   /* Return the smallest element of a 1D REAL array. */
   if (n <= 0) return 0.0f;
   float m = x[0];
   for (int i = 1; i < n; ++i) if (x[i] < m) m = x[i];
   return m;
}


double minval_1d_double(int n, const double *x) {
   /* Return the smallest element of a 1D DOUBLE PRECISION array. */
   if (n <= 0) return 0.0;
   double m = x[0];
   for (int i = 1; i < n; ++i) if (x[i] < m) m = x[i];
   return m;
}


int minval_1d_int(int n, const int *x) {
   /* Return the smallest element of a 1D INTEGER array. */
   if (n <= 0) return 0;
   int m = x[0];
   for (int i = 1; i < n; ++i) if (x[i] < m) m = x[i];
   return m;
}


float maxval_1d_float(int n, const float *x) {
   /* Return the largest element of a 1D REAL array. */
   if (n <= 0) return 0.0f;
   float m = x[0];
   for (int i = 1; i < n; ++i) if (x[i] > m) m = x[i];
   return m;
}


double maxval_1d_double(int n, const double *x) {
   /* Return the largest element of a 1D DOUBLE PRECISION array. */
   if (n <= 0) return 0.0;
   double m = x[0];
   for (int i = 1; i < n; ++i) if (x[i] > m) m = x[i];
   return m;
}


int maxval_1d_int(int n, const int *x) {
   /* Return the largest element of a 1D INTEGER array. */
   if (n <= 0) return 0;
   int m = x[0];
   for (int i = 1; i < n; ++i) if (x[i] > m) m = x[i];
   return m;
}


int count_1d_int(int n, const int *x) {
   /* Count nonzero elements of a 1D LOGICAL/INTEGER mask array. */
   int c = 0;
   for (int i = 0; i < n; ++i) if (x[i]) ++c;
   return c;
}


int any_1d_int(int n, const int *x) {
   /* Return whether any element of a 1D LOGICAL/INTEGER mask is true. */
   for (int i = 0; i < n; ++i) if (x[i]) return 1;
   return 0;
}


int all_1d_int(int n, const int *x) {
   /* Return whether every element of a 1D LOGICAL/INTEGER mask is true. */
   for (int i = 0; i < n; ++i) if (!x[i]) return 0;
   return 1;
}


int any_eq_1d_int(int n, int u, const int *v) {
   /* Return whether any 1D INTEGER/LOGICAL element equals a scalar. */
   for (int i = 0; i < n; ++i) if (u == v[i]) return 1;
   return 0;
}


int any_eq_1d_float(int n, float u, const float *v) {
   /* Return whether any 1D REAL element equals a scalar. */
   for (int i = 0; i < n; ++i) if (u == v[i]) return 1;
   return 0;
}


int any_eq_1d_double(int n, double u, const double *v) {
   /* Return whether any 1D DOUBLE PRECISION element equals a scalar. */
   for (int i = 0; i < n; ++i) if (u == v[i]) return 1;
   return 0;
}


int any_eq_1d_string(int n, const char *u, char *const *v) {
   /* Return whether any 1D CHARACTER element equals a scalar, ignoring trailing blanks. */
   int nu = len_trim_s(u);
   for (int i = 0; i < n; ++i) {
      int nv = len_trim_s(v[i]);
      if (nu == nv && strncmp(u, v[i], (size_t) nu) == 0) return 1;
   }
   return 0;
}


int any_eq_1d_charbuf(int n, int elem_len, const char *u, const char *v) {
   /* Return whether any fixed-length CHARACTER buffer element equals a scalar, ignoring trailing blanks. */
   int nu = len_trim_s(u);
   int stride = elem_len + 1;
   for (int i = 0; i < n; ++i) {
      const char *vi = v + i * stride;
      int nv = len_trim_s(vi);
      if (nu == nv && strncmp(u, vi, (size_t) nu) == 0) return 1;
   }
   return 0;
}


float dot_product_1d_float(int n, const float *x, const float *y) {
   /* Compute the dot product of two 1D REAL arrays. */
   float s = 0.0f;
   for (int i = 0; i < n; ++i) s += x[i] * y[i];
   return s;
}


double dot_product_1d_double(int n, const double *x, const double *y) {
   /* Compute the dot product of two 1D DOUBLE PRECISION arrays. */
   double s = 0.0;
   for (int i = 0; i < n; ++i) s += x[i] * y[i];
   return s;
}


int dot_product_1d_int(int n, const int *x, const int *y) {
   /* Compute the dot product of two 1D INTEGER arrays. */
   int s = 0;
   for (int i = 0; i < n; ++i) s += x[i] * y[i];
   return s;
}
