\ This file was automatically generated by Zimpl
\ param N := 4;
\ set C := { 1 .. N };
\ set CxC := C * C;
\ var x[CxC] binary;
\ maximize reinas:   sum <i, j> in CxC : x[i, j];
\ subto row:   forall <i> in C do sum <i, j> in CxC : x[i, j] <= 1;
\ subto col:   forall <j> in C do sum <i, j> in CxC : x[i, j] <= 1;
\ subto diag_row_do:   forall <i> in C do sum <m, n> in CxC with m - i == n - 1 : x[m, n] <= 1;
\ subto diag_row_up:   forall <i> in C do sum <m, n> in CxC with m - i == 1 - n : x[m, n] <= 1;
\ subto diag_col_do:   forall <j> in C do sum <m, n> in CxC with m - 1 == n - j : x[m, n] <= 1;
\ subto diag_col_up:   forall <j> in C do sum <m, n> in CxC with card(C) - m == n - j : x[m, n] <= 1;
\Problem name: reinas.zpl
Maximize
 reinas:  + x#1#1 + x#1#2 + x#1#3 + x#1#4 + x#2#1 + x#2#2
  + x#2#3 + x#2#4 + x#3#1 + x#3#2 + x#3#3 + x#3#4
  + x#4#1 + x#4#2 + x#4#3 + x#4#4
Subject to
 row_1:
  + x#1#4 + x#1#3 + x#1#2 + x#1#1 <= 1
 row_2:
  + x#2#4 + x#2#3 + x#2#2 + x#2#1 <= 1
 row_3:
  + x#3#4 + x#3#3 + x#3#2 + x#3#1 <= 1
 row_4:
  + x#4#4 + x#4#3 + x#4#2 + x#4#1 <= 1
 col_1:
  + x#4#1 + x#3#1 + x#2#1 + x#1#1 <= 1
 col_2:
  + x#4#2 + x#3#2 + x#2#2 + x#1#2 <= 1
 col_3:
  + x#4#3 + x#3#3 + x#2#3 + x#1#3 <= 1
 col_4:
  + x#4#4 + x#3#4 + x#2#4 + x#1#4 <= 1
 diag_row_do_1:
  + x#4#4 + x#3#3 + x#2#2 + x#1#1 <= 1
 diag_row_do_2:
  + x#4#3 + x#3#2 + x#2#1 <= 1
 diag_row_do_3:
  + x#4#2 + x#3#1 <= 1
 diag_row_do_4:
  + x#4#1 <= 1
 diag_row_up_1:
  + x#1#1 <= 1
 diag_row_up_2:
  + x#2#1 + x#1#2 <= 1
 diag_row_up_3:
  + x#3#1 + x#2#2 + x#1#3 <= 1
 diag_row_up_4:
  + x#4#1 + x#3#2 + x#2#3 + x#1#4 <= 1
 diag_col_do_1:
  + x#4#4 + x#3#3 + x#2#2 + x#1#1 <= 1
 diag_col_do_2:
  + x#3#4 + x#2#3 + x#1#2 <= 1
 diag_col_do_3:
  + x#2#4 + x#1#3 <= 1
 diag_col_do_4:
  + x#1#4 <= 1
 diag_col_up_1:
  + x#4#1 + x#3#2 + x#2#3 + x#1#4 <= 1
 diag_col_up_2:
  + x#4#2 + x#3#3 + x#2#4 <= 1
 diag_col_up_3:
  + x#4#3 + x#3#4 <= 1
 diag_col_up_4:
  + x#4#4 <= 1
Bounds
 0 <= x#1#1 <= 1
 0 <= x#1#2 <= 1
 0 <= x#1#3 <= 1
 0 <= x#1#4 <= 1
 0 <= x#2#1 <= 1
 0 <= x#2#2 <= 1
 0 <= x#2#3 <= 1
 0 <= x#2#4 <= 1
 0 <= x#3#1 <= 1
 0 <= x#3#2 <= 1
 0 <= x#3#3 <= 1
 0 <= x#3#4 <= 1
 0 <= x#4#1 <= 1
 0 <= x#4#2 <= 1
 0 <= x#4#3 <= 1
 0 <= x#4#4 <= 1
General
 x#1#1
 x#1#2
 x#1#3
 x#1#4
 x#2#1
 x#2#2
 x#2#3
 x#2#4
 x#3#1
 x#3#2
 x#3#3
 x#3#4
 x#4#1
 x#4#2
 x#4#3
 x#4#4
End
