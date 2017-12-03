
param N := 4;

set C := { 1 .. N };
set CxC := C * C;
var x[CxC] binary;

maximize reinas:
  sum <i, j> in CxC : x[i, j];

subto row:
  forall <i> in C do sum <i, j> in CxC : x[i, j] <= 1;

subto col:
  forall <j> in C do sum <i, j> in CxC : x[i, j] <= 1;

subto diag_row_do:
  forall <i> in C do sum <m, n> in CxC with m - i == n - 1 : x[m, n] <= 1;

subto diag_row_up:
  forall <i> in C do sum <m, n> in CxC with m - i == 1 - n : x[m, n] <= 1;

subto diag_col_do:
  forall <j> in C do sum <m, n> in CxC with m - 1 == n - j : x[m, n] <= 1;

subto diag_col_up:
  forall <j> in C do sum <m, n> in CxC with card(C) - m == n - j : x[m, n] <= 1;
