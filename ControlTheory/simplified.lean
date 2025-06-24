import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

open Matrix

-- Define state vector as fixed 2D
def StateVector := Fin 2 → ℝ
-- Input vector remains arbitrary dimension
def InputVector (p : ℕ) := Fin p → ℝ

-- Discrete system with 2x2 state matrix
structure DiscreteLinearSystemState (p : ℕ) where
  A : Matrix (Fin 2) (Fin 2) ℝ  -- Fixed 2x2 state matrix
  B : Matrix (Fin 2) (Fin p) ℝ  -- Input matrix (2×p)
  x : ℕ → StateVector           -- State sequence
  u : ℕ → InputVector p         -- Input sequence

-- System equation for 2D states
def state_system_equation {p : ℕ} (sys : DiscreteLinearSystemState p) : Prop :=
  ∀ k : ℕ, sys.x (k + 1) = sys.A.mulVec (sys.x k) + sys.B.mulVec (sys.u k)

-- Output vector arbitrary dimension
def OutputVector (q : ℕ) := Fin q → ℝ

-- Output system with 2D states
structure DiscreteLinearSystemOutput (p q : ℕ) where
  C : Matrix (Fin q) (Fin 2) ℝ  -- Output matrix (q×2)
  D : Matrix (Fin q) (Fin p) ℝ  -- Feedthrough matrix (q×p)
  y : ℕ → OutputVector q        -- Output sequence
  u : ℕ → InputVector p         -- Input sequence
  x : ℕ → StateVector           -- State sequence (2D)

-- Output equation for 2D states
def output_system_equation {p q: ℕ} (sys : DiscreteLinearSystemOutput p q) : Prop :=
  ∀ k : ℕ, sys.y k = sys.C.mulVec (sys.x k) + sys.D.mulVec (sys.u k)

-- Example 2x2 matrix
def mat2 : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![1, 2],
    ![3, 4]]

-- Eigenvalue calculation for 2x2 matrices
def eigenvalues2 (A : Matrix (Fin 2) (Fin 2) ℝ) : Set ℝ :=
  let a00 := A 0 0
  let a01 := A 0 1
  let a10 := A 1 0
  let a11 := A 1 1
  let trace := a00 + a11
  let det := a00 * a11 - a01 * a10
  let disc := trace^2 - 4 * det
  if h : disc ≥ 0 then
    let sqrt_disc := Real.sqrt disc
    {(trace + sqrt_disc)/2, (trace - sqrt_disc)/2}
  else ∅

#check eigenvalues2 mat2  -- Now works for 2x2
