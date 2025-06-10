import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Tower
import Mathlib.Data.Finite.Sum
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.RingTheory.AlgebraTower
import Mathlib.RingTheory.Ideal.Span
import Mathlib.LinearAlgebra.Matrix.ToLin
-- Matrix is defined as: Matrix m n α := m → n → α
-- where m and n are the index types (rows and columns)
-- and α is the element type

-- Example 1: 2x3 matrix of natural numbers
def mat1 : Matrix (Fin 3) (Fin 3) ℕ :=
  ![![1, 2, 3],
    ![4, 5, 6],
    ![7, 8, 9]]




def f' : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) := Matrix.toLin' mat1
