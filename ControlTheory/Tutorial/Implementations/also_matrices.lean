import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Notation

def myMatrix : Matrix (Fin 2) (Fin 3) ℝ :=
  Matrix.of (λ i j =>
    match i, j with
    | 0, 0 => 1.0
    | 0, 1 => 2.0
    | 0, 2 => 3.0
    | 1, 0 => 4.0
    | 1, 1 => 5.0
    | 1, 2 => 6.0)

#check myMatrix  -- outputs: 3.0

#eval myMatrix 0 2

def myMatrix2 : Matrix (Fin 2) (Fin 3) ℝ :=
  !![1.0, 2.0, 3.0; 4.0, 5.0, 6.0]

#eval myMatrix2 1 1
#check myMatrix2
#check myMatrix2 1 1


def myMatrix_clean : Matrix (Fin 2) (Fin 3) Float :=
  !![1.0, 2.0, 3.0;
     4.0, 5.0, 6.0]

#eval myMatrix_clean 1 2  -- outputs: 6.000000
