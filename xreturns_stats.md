# xreturns_stats
`c:\Programs\Python313\python.exe xf2c.py xreturns_stats.f90 --run-both`

## Fortran

```fortran
module price_stats_mod
implicit none

integer, parameter :: dp = kind(1.0d0)

contains

function count_fields(line) result(nfields)
! count comma-separated fields
character(len=*), intent(in) :: line
integer :: nfields
integer :: i
nfields = 1
do i = 1, len_trim(line)
   if (line(i:i) == ',') nfields = nfields + 1
end do
end function count_fields

subroutine split_csv_line(line, fields)
! split a csv line on commas
character(len=*), intent(in) :: line
character(len=*), intent(out) :: fields(:)
integer :: i, i0, k, n, lt

n = size(fields)
fields = ''
lt = len_trim(line)
i0 = 1
k = 1

do i = 1, lt
   if (line(i:i) == ',') then
      if (k <= n) fields(k) = adjustl(line(i0:i-1))
      k = k + 1
      i0 = i + 1
   end if
end do

if (k <= n) fields(k) = adjustl(line(i0:lt))
end subroutine split_csv_line

function mean(x) result(mu)
! return the mean of a real vector
real(kind=dp), intent(in) :: x(:)
real(kind=dp) :: mu
mu = sum(x) / real(size(x), kind=dp)
end function mean

function sd(x) result(sig)
! return the sample standard deviation of a real vector
real(kind=dp), intent(in) :: x(:)
real(kind=dp) :: sig
real(kind=dp) :: mu
if (size(x) <= 1) then
   sig = 0.0_dp
else
   mu = mean(x)
   sig = sqrt(sum((x - mu)**2) / real(size(x) - 1, kind=dp))
end if
end function sd

subroutine print_corr_matrix(x, names)
! print the sample correlation matrix of the columns of x
real(kind=dp), intent(in) :: x(:, :)
character(len=*), intent(in) :: names(:)
real(kind=dp), allocatable :: mu(:), sig(:), corr(:, :)
integer :: nobs, nvar, i, j
nobs = size(x, 1)
nvar = size(x, 2)
if (size(names) /= nvar) error stop "size(names) must match number of columns of x"
if (nobs <= 1) error stop "need at least two rows to compute correlations"

allocate(mu(nvar), sig(nvar), corr(nvar, nvar))

do j = 1, nvar
   mu(j) = mean(x(:, j))
   sig(j) = sd(x(:, j))
end do

do i = 1, nvar
   do j = 1, nvar
      if (sig(i) == 0.0_dp .or. sig(j) == 0.0_dp) then
         corr(i, j) = 0.0_dp
      else
         corr(i, j) = sum((x(:, i) - mu(i)) * (x(:, j) - mu(j))) / &
                      (real(nobs - 1, kind=dp) * sig(i) * sig(j))
      end if
   end do
end do

write(*, "(/,a)") "correlation matrix of returns"
write (*,"(*(a8))") "", (trim(names(j)), j = 1, nvar)
do i = 1, nvar
   write(*, "(a8,*(f8.3))") trim(names(i)), corr(i,:) ! (corr(i, j), j = 1, nvar)
end do

end subroutine print_corr_matrix

end module price_stats_mod

program price_return_stats
use price_stats_mod, only: dp, count_fields, split_csv_line, mean, sd, print_corr_matrix
implicit none
character(len=256) :: filename
character(len=4096) :: line
character(len=32) :: first_date, last_date
character(len=64), allocatable :: names(:)
character(len=256), allocatable :: fields(:)
real(kind=dp), allocatable :: prices(:,:), rets(:,:), mu(:), sig(:)
integer :: iu, ios, n_assets, nobs, i, j
real(kind=dp), parameter :: ret_scale = 100.0_dp
call get_command_argument(1, filename)
if (len_trim(filename) == 0) filename = "spy_efa_eem_tlt_lqd.csv"

open(newunit=iu, file=trim(filename), status="old", action="read", iostat=ios)
if (ios /= 0) error stop "cannot open input file"
if (ret_scale /= 1.0_dp) print "('return scaling: ',f0.4)", ret_scale
read(iu, "(a)", iostat=ios) line
if (ios /= 0) error stop "cannot read header line"

n_assets = count_fields(line) - 1
if (n_assets <= 0) error stop "no asset columns found"

nobs = 0
do
   read(iu, "(a)", iostat=ios) line
   if (ios /= 0) exit
   if (len_trim(line) > 0) nobs = nobs + 1
end do
close(iu)

if (nobs < 2) error stop "need at least two price rows"

allocate(names(n_assets))
allocate(fields(n_assets + 1))
allocate(prices(nobs, n_assets))
allocate(mu(n_assets), sig(n_assets))
first_date = ""
last_date = ""

open(newunit=iu, file=filename, status="old", action="read", iostat=ios)
if (ios /= 0) error stop "cannot reopen input file " // trim(filename)
print "('prices file: ',a)", trim(filename)

read(iu, "(a)", iostat=ios) line
if (ios /= 0) error stop "cannot reread header line"

call split_csv_line(trim(line), fields)
names = fields(2:)

do i = 1, nobs
   read(iu, "(a)", iostat=ios) line
   if (ios /= 0) error stop "unexpected end of file while reading prices"
   call split_csv_line(trim(line), fields)
   if (i == 1) first_date = trim(fields(1))
   last_date = trim(fields(1))
   do j = 1, n_assets
      read(fields(j + 1), *, iostat=ios) prices(i, j)
      if (ios /= 0) then
         write(*,"(a,i0,a,i0)") "error reading price at row ", i, ", column ", j
         error stop
      end if
   end do
end do
close(iu)

print "('date range: ',a,' to ',a)", trim(first_date), trim(last_date)
print "('# days read: ',i0)", nobs

rets = ret_scale * (prices(2:nobs, :) / prices(1:nobs - 1, :) - 1.0_dp)

do j = 1, n_assets
   mu(j) = mean(rets(:, j))
   sig(j) = sd(rets(:, j))
end do

write (*,"(*(a8))") "symbol", "mean", "sd"
do j = 1, n_assets
   write(*, "(a8, *(f8.4))") trim(names(j)), mu(j), sig(j)
end do

call print_corr_matrix(rets, names)

end program price_return_stats
```

## Fortran Output

```text
return scaling: 100.0000
prices file: spy_efa_eem_tlt_lqd.csv
date range: 2003-04-14 to 2022-06-17
# days read: 4830
  symbol    mean      sd
     SPY  0.0441  1.1927
     EFA  0.0338  1.3501
     EEM  0.0495  1.7966
     TLT  0.0223  0.8888
     LQD  0.0181  0.5263

correlation matrix of returns
             SPY     EFA     EEM     TLT     LQD
     SPY   1.000   0.891   0.832  -0.376   0.151
     EFA   0.891   1.000   0.874  -0.349   0.182
     EEM   0.832   0.874   1.000  -0.312   0.142
     TLT  -0.376  -0.349  -0.312   1.000   0.494
     LQD   0.151   0.182   0.142   0.494   1.000
```

## Generated C

```c
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <complex.h>
#include <float.h>
#include <limits.h>
#include <string.h>

#include "fortran_runtime.h"

double mean(const int n, double *x); /* return the mean of a real vector */
double sd(const int n, double *x); /* return the sample standard deviation of a real vector */
void print_corr_matrix(const int n_x_1, const int n_x_2, double *x, const int n, char **names); /* print the sample correlation matrix of the columns of x */

double mean(const int n, double *x) {
   /* return the mean of a real vector */
   /* n: extent of x (dimension 1) */
   double mu;
   {
      double red = 0.0;
      for (int i_fill = 0; i_fill < n; ++i_fill) red += x[i_fill];
      mu = red / ((double) n);
   }
   return mu;
}

double sd(const int n, double *x) {
   /* return the sample standard deviation of a real vector */
   /* n: extent of x (dimension 1) */
   double sig, mu;
   if (n <= 1) {
      sig = 0.0;
   }
   else {
      mu = mean(n, x);
      {
         double red = 0.0;
         for (int i_fill = 0; i_fill < n; ++i_fill) red += (((x[i_fill] - mu)) * ((x[i_fill] - mu)));
         sig = (sqrt(red / ((double) (n - 1))));
      }
   }
   return sig;
}

void print_corr_matrix(const int n_x_1, const int n_x_2, double *x, const int n, char **names) {
   /* print the sample correlation matrix of the columns of x */
   /* n_x_1: extent of x (dimension 1) */
   /* n_x_2: extent of x (dimension 2) */
   /* n: extent of names (dimension 1) */
   double *mu = NULL, *sig = NULL, *corr = NULL;
   int n_mu = 0, n_sig = 0, n_corr_1 = 0, n_corr_2 = 0, i, j;
   if (n != n_x_2) {
      fprintf(stderr, "%s\n", "size(names) must match number of columns of x");
      exit(1);
   }
   if (n_x_1 <= 1) {
      fprintf(stderr, "%s\n", "need at least two rows to compute correlations");
      exit(1);
   }
   if (mu) free(mu);
   mu = (double*) malloc(sizeof(double) * n_x_2);
   if (!mu && n_x_2 > 0) return;
   n_mu = n_x_2;
   if (sig) free(sig);
   sig = (double*) malloc(sizeof(double) * n_x_2);
   if (!sig && n_x_2 > 0) return;
   n_sig = n_x_2;
   if (corr) free(corr);
   corr = (double*) malloc(sizeof(double) * ((n_x_2 * n_x_2)));
   if (!corr && ((n_x_2 * n_x_2)) > 0) return;
   n_corr_1 = n_x_2;
   n_corr_2 = n_x_2;
   j = 0;
   while (j < n_x_2) {
      mu[j] = mean(n_x_1, &x[n_x_1 * j]);
      sig[j] = sd(n_x_1, &x[n_x_1 * j]);
      j += 1;
   }
   xf2c_loop_1_break: ;
   i = 0;
   while (i < n_x_2) {
      j = 0;
      while (j < n_x_2) {
         if (sig[i] == 0.0 || sig[j] == 0.0) {
            corr[i + n_corr_1 * j] = 0.0;
         }
         else {
            {
               double red = 0.0;
               for (int i_fill = 0; i_fill < n_x_1; ++i_fill) red += (x[i_fill + n_x_1 * i] - mu[i]) * (x[i_fill + n_x_1 * j] - mu[j]);
               corr[i + n_corr_1 * j] = red /                       (((double) (n_x_1 - 1)) * sig[i] * sig[j]);
            }
         }
         j += 1;
      }
      i += 1;
   }
   printf("\n");
   printf("%s", "correlation matrix of returns");
   printf("\n");
   printf("%8s", "");
   {
      for (j = 1; j <= n_x_2; ++j) {
         printf("%8s", trim_s(names[j - 1]));
      }
      printf("\n");
   }
   i = 1;
   while (i <= n_x_2) {
      /* (corr(i, j), j = 1, n_x_2) */
      printf("%8s", trim_s(names[i - 1]));
      for (int j_fmt = 0; j_fmt < n_corr_2; ++j_fmt) {
         printf("%8.3f", corr[i - 1 + n_corr_1 * j_fmt]);
      }
      printf("\n");
      i += 1;
   }
}

int main(int argc, char **argv) {
   enum { filename_len = 256, line_len = 4096, first_date_len = 32, last_date_len = 32 };
   char filename[filename_len + 1] = "", line[line_len + 1] = "", first_date[first_date_len + 1] = "";
   char last_date[last_date_len + 1] = "";
   char **names = NULL, **fields = NULL;
   int n_names = 0, n_fields = 0, n_prices_1 = 0, n_prices_2 = 0, n_rets_1 = 0, n_rets_2 = 0, n_mu = 0;
   int n_sig = 0, iu, ios, n_assets, nobs, i, j;
   double *prices = NULL, *rets = NULL, *mu = NULL, *sig = NULL;
   const double ret_scale = 100.0;
   assign_str(filename, filename_len, (1 < argc) ? argv[1] : "");
   if (len_trim_s(filename) == 0) assign_str(filename, filename_len, "spy_efa_eem_tlt_lqd.csv");
   iu = alloc_unit();
   ios = open_unit(iu, trim_s(trim_s(filename)), "read", "old");
   if (ios != 0) {
      fprintf(stderr, "%s\n", "cannot open input file");
      return 1;
   }
   if (ret_scale != 1.0) {
      printf("%s", "return scaling: ");
      printf("%.4f", ret_scale);
      printf("\n");
   }
   ios = read_a(iu, line, line_len);
   if (ios != 0) {
      fprintf(stderr, "%s\n", "cannot read header line");
      return 1;
   }
   n_assets = count_fields(line) - 1;
   if (n_assets <= 0) {
      fprintf(stderr, "%s\n", "no asset columns found");
      return 1;
   }
   nobs = 0;
   while (1) {
      ios = read_a(iu, line, line_len);
      if (ios != 0) goto xf2c_loop_1_break;
      if (len_trim_s(line) > 0) nobs = nobs + 1;
   }
   xf2c_loop_1_break: ;
   close_unit(iu);
   if (nobs < 2) {
      fprintf(stderr, "%s\n", "need at least two price rows");
      return 1;
   }
   if (names) free_str_array(names, n_names);
   names = (char**) malloc(sizeof(char*) * n_assets);
   if (!names && n_assets > 0) return 1;
   for (int i_fill = 0; i_fill < n_assets; ++i_fill) names[i_fill] = NULL;
   n_names = n_assets;
   for (int i_fill = 0; i_fill < n_assets; ++i_fill) assign_str_alloc(&names[i_fill], "");
   if (fields) free_str_array(fields, n_fields);
   fields = (char**) malloc(sizeof(char*) * (n_assets + 1));
   if (!fields && (n_assets + 1) > 0) return 1;
   for (int i_fill = 0; i_fill < (n_assets + 1); ++i_fill) fields[i_fill] = NULL;
   n_fields = n_assets + 1;
   for (int i_fill = 0; i_fill < (n_assets + 1); ++i_fill) assign_str_alloc(&fields[i_fill], "");
   if (prices) free(prices);
   prices = (double*) malloc(sizeof(double) * ((nobs * n_assets)));
   if (!prices && ((nobs * n_assets)) > 0) return 1;
   n_prices_1 = nobs;
   n_prices_2 = n_assets;
   if (mu) free(mu);
   mu = (double*) malloc(sizeof(double) * n_assets);
   if (!mu && n_assets > 0) return 1;
   n_mu = n_assets;
   if (sig) free(sig);
   sig = (double*) malloc(sizeof(double) * n_assets);
   if (!sig && n_assets > 0) return 1;
   n_sig = n_assets;
   assign_str(first_date, first_date_len, "");
   assign_str(last_date, last_date_len, "");
   iu = alloc_unit();
   ios = open_unit(iu, trim_s(filename), "read", "old");
   if (ios != 0) {
      fprintf(stderr, "%s\n", concat_s2("cannot reopen input file ", trim_s(filename)));
      return 1;
   }
   printf("%s", "prices file: ");
   printf("%s", trim_s(filename));
   printf("\n");
   ios = read_a(iu, line, line_len);
   if (ios != 0) {
      fprintf(stderr, "%s\n", "cannot reread header line");
      return 1;
   }
   char *arg_str_0 = copy_str_s(trim_s(line));
   split_csv_line(arg_str_0, n_fields, fields);
   if (arg_str_0) free(arg_str_0);
   {
      int n_tmp = 0;
      if (1 > 0) {
         for (int i_fill = 2; i_fill <= n_fields; i_fill += 1) ++n_tmp;
      } else {
         for (int i_fill = 2; i_fill >= n_fields; i_fill += 1) ++n_tmp;
      }
      if (names) free_str_array(names, n_names);
      names = (char**) malloc(sizeof(char*) * n_tmp);
      if (!names && n_tmp > 0) return 1;
      for (int p_fill = 0; p_fill < n_tmp; ++p_fill) names[p_fill] = NULL;
      n_names = n_tmp;
      for (int p_fill = 0; p_fill < n_tmp; ++p_fill) {
         assign_str_alloc(&names[p_fill], fields[2 + p_fill - 1]);
      }
   }
   i = 1;
   while (i <= nobs) {
      ios = read_a(iu, line, line_len);
      if (ios != 0) {
         fprintf(stderr, "%s\n", "unexpected end of file while reading prices");
         return 1;
      }
      char *arg_str_0 = copy_str_s(trim_s(line));
      split_csv_line(arg_str_0, n_fields, fields);
      if (arg_str_0) free(arg_str_0);
      if (i == 1) assign_str(first_date, first_date_len, trim_s(fields[0]));
      assign_str(last_date, last_date_len, trim_s(fields[0]));
      j = 1;
      while (j <= n_assets) {
         ios = read_first_double_s(fields[j + 1 - 1], &(prices[i - 1 + n_prices_1 * (j - 1)]));
         if (ios != 0) {
            printf("%s", "error reading price at row ");
            printf("%d", i);
            printf("%s", ", column ");
            printf("%d", j);
            printf("\n");
            return 1;
         }
         j += 1;
      }
      i += 1;
   }
   close_unit(iu);
   printf("%s", "date range: ");
   printf("%s", trim_s(first_date));
   printf("%s", " to ");
   printf("%s", trim_s(last_date));
   printf("\n");
   printf("%s", "# days read: ");
   printf("%d", nobs);
   printf("\n");
   if (rets) free(rets);
   rets = (double*) malloc(sizeof(double) * (((((nobs - 2) / 1 + 1)) * (((((1 + n_prices_2 - 1)) - 1) / 1 + 1)))));
   if (!rets && (((((nobs - 2) / 1 + 1)) * (((((1 + n_prices_2 - 1)) - 1) / 1 + 1)))) > 0) return 1;
   n_rets_1 = ((nobs - 2) / 1 + 1);
   n_rets_2 = ((((1 + n_prices_2 - 1)) - 1) / 1 + 1);
   for (int i2_fill = 0; i2_fill < ((((1 + n_prices_2 - 1)) - 1) / 1 + 1); ++i2_fill) {
      for (int i1_fill = 0; i1_fill < ((nobs - 2) / 1 + 1); ++i1_fill) {
         rets[i1_fill + (((nobs - 2) / 1 + 1)) * i2_fill] = ret_scale * (prices[2 + i1_fill - 1 + n_prices_1 * (1 + i2_fill - 1)] / prices[1 + i1_fill - 1 + n_prices_1 * (1 + i2_fill - 1)] - 1.0);
      }
   }
   j = 0;
   while (j < n_assets) {
      mu[j] = mean(n_rets_1, &rets[n_rets_1 * j]);
      sig[j] = sd(n_rets_1, &rets[n_rets_1 * j]);
      j += 1;
   }
   printf("%8s", "symbol");
   printf("%8s", "mean");
   printf("%8s", "sd");
   printf("\n");
   j = 0;
   while (j < n_assets) {
      printf("%8s", trim_s(names[j]));
      printf("%8.4f", mu[j]);
      printf("%8.4f", sig[j]);
      printf("\n");
      j += 1;
   }
   print_corr_matrix(n_rets_1, n_rets_2, rets, n_names, names);
   free_str_array(names, n_names);
   free_str_array(fields, n_fields);
   free(prices);
   free(rets);
   free(mu);
   free(sig);
   return 0;
}
```

## C Output

```text
return scaling: 100.0000
prices file: spy_efa_eem_tlt_lqd.csv
date range: 2003-04-14 to 2022-06-17
# days read: 4830
  symbol    mean      sd
     SPY  0.0441  1.1927
     EFA  0.0338  1.3501
     EEM  0.0495  1.7966
     TLT  0.0223  0.8888
     LQD  0.0181  0.5263

correlation matrix of returns
             SPY     EFA     EEM     TLT     LQD
     SPY   1.000   0.891   0.832  -0.376   0.151
     EFA   0.891   1.000   0.874  -0.349   0.182
     EEM   0.832   0.874   1.000  -0.312   0.142
     TLT  -0.376  -0.349  -0.312   1.000   0.494
     LQD   0.151   0.182   0.142   0.494   1.000
```
