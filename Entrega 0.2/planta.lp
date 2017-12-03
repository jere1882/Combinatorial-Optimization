/* Variables */

// xj : cantidad de jamones no ahumados producidos
// xl : cantidad de lomos no ahumados producidos
// xs : cantidad de salchichas no ahumadas producidas

// xja: cantidad de jamones ahumados producidos (sin emplear horas extra)
// xla: cantidad de lomos ahumados producidos (sin emplear horas extra)
// xsa: cantidad de salchichas ahumadas producidas (sin emplear horas extra)

// xje: cantidad de jamones ahumados en horas extra
// xle: cantidad de lomos ahumados en horas extra
// xse: cantidad de salchichas ahumadas en horas extra

// j : se enciende la máquina J (variable de decisión, 0-1)
// l : se enciende la máquina L (variable de decisión, 0-1)
// s : se enciende la máquina S (variable de decisión, 0-1)

/* Objective function */
MAX: 8 xj + 4 xl + 4 xs + 14 xja + 12 xla + 13 xsa + 11 xje + 7 xle + 9 xse - 50j - 50l - 50s;

/* Variable bounds */

xj + xja + xje - 10 j <= 480;  // Producción de jamones
xl + xla + xle - 40 l <= 400;  // producción de lomos
xs + xsa + xse - 20 s <= 230;  // producción de salchichas

xja + xla + xsa <= 420;       // capacidad de ahumado
xje + xle + xse <= 250;       // capacidad de ahumado extra

xj  >=0;
xja >=0;
xje >=0;
xl  >=0;
xla >=0;
xle >=0;
xs  >=0;
xsa >=0;
xse >=0;

0 <= j <= 1;
0 <= s <= 1;
0 <= l <= 1;
                     //         J L S
j + l + s <= 2;      // evita   1 1 1
j <= l + s;          // evita   1 0 0
l <= j + s;          // evita   0 1 0

int j;
int s;
int l;

