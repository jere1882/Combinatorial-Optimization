/* Objective function */
min: 1.84 x1 + 2.19 x2 + 1.84 x3 + 1.44 x4 + 2.29 x5 + 0.77 x6 + 1.29 x7 + 0.60 x8 + 0.72 x9;
//min: 510 x1 + 370 x2 + 500 x3 + 370 x4 + 400 x5 + 220 x6 + 345 x7 + 110 x8 + 80 x9 ;
/* Variable bounds */

510 x1 + 370 x2 + 500 x3 + 370 x4 + 400 x5 + 220 x6 + 345 x7 + 110 x8 + 80 x9 >= 2000;
34 x1  + 35 x2  + 42 x3 + 38 x4 + 42 x5 + 26 x6 + 27 x7 + 12 x8 + 20 x9 >= 350;
34 x1  + 35 x2  + 42 x3 + 38 x4 + 42 x5 + 26 x6 + 27 x7 + 12 x8 + 20 x9 <= 375;
28 x1  + 24 x2  + 25 x3 + 14 x4 + 31 x5 + 3 x6   + 15 x7 + 9 x8 + 1 x9 >= 55;
15 x1  + 15 x2  + 6 x3 + 2 x4 + 8 x5 + 0 x6     + 4 x7 + 10 x8 + 2 x9 >= 100;
6 x1   + 10 x2  + 2 x3 + 0 x4 + 15 x5 + 15 x6  + 0 x7 + 4 x8 + 120 x9 >= 100;
30 x1  + 20 x2  + 25 x3 + 15 x4 + 15 x5 + 0 x6 + 20 x7 + 30 x8 + 2 x9 >= 100;
20 x1  + 20 x2  + 20 x3 + 10 x4 + 8 x5 + 2 x6  +  15 x7 + 0 x8 + 2 x9 >= 100;

x1>=0;
x2>=0;
x3>=0;
x4>=0;
x5>=0;
x6>=0;
x7>=0;
x8>=0;
x9>=0;



x1 <= 2;
x2 <= 2;
x3 <= 2;
x4 <= 2;
x5 <= 2;
x6 <= 2;
x7 <= 2;
x8 <= 2;
x9 <= 2;

/*
2. 4.385 * 510 + 6.148 * 220 + 3.422 * 110 = 3965.33
3. descomentar segunda linea    16.67
4. comentar la primera y descomentar la 3era (infactible)
5. comentar todas las restricciones de calorias (2467)
6. descomentar todos los x<=2 (precio = 16.77 y calorias = 3488)
*/


  //
//510 x1 + 370 x2 + 500 x3 + 370 x4 + 400 x5 + 220 x6 + 345 x7 + 110 x8 + 80 x9 <= 2500;
// 510 x1 + 370 x2 + 500 x3 + 370 x4 + 400 x5 + 220 x6 + 345 x7 + 110 x8 + 80 x9 <= 2000;
