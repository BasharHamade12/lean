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
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Complex.Norm
import Mathlib.Data.Matrix.Defs
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Matrix
import Mathlib.Analysis.CStarAlgebra.CStarMatrix

variable {R : Type*} [NormedField R]
variable {A : Type*}
variable {n : ℕ}

open scoped ComplexOrder

def spectral_radius_less_than_one3 [NormedRing A] [NormedAlgebra ℂ A] (a : A) : Prop :=
  spectralRadius ℂ a < 1




theorem gelfand_le_one_when_spectral_radius_le_one
    [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] (a : A) :
    spectral_radius_less_than_one3 a →
    Filter.limsup (fun (n : ℕ) => (‖a ^ n‖₊ : ENNReal) ^ (1 / n : ℝ)) Filter.atTop < 1 := by
  intro h_spectral
  unfold spectral_radius_less_than_one3 at h_spectral

  have h_gelfand := spectrum.limsup_pow_nnnorm_pow_one_div_le_spectralRadius a

  convert lt_of_le_of_lt h_gelfand h_spectral





abbrev StateVector (n : ℕ) := Fin n → ℂ
abbrev InputVector (p : ℕ) := Fin p → ℂ
abbrev InputMatrix (n p : ℕ) :=   CStarMatrix (Fin n) (Fin p) ℂ


abbrev StateMatrix (n : ℕ) := CStarMatrix (Fin n) (Fin n) ℂ



noncomputable instance (n : ℕ) : Ring (StateMatrix n) := Matrix.instRing


noncomputable instance (n : ℕ) : SeminormedAddCommGroup (StateMatrix n) := Matrix.seminormedAddCommGroup


noncomputable instance (n : ℕ) : NormedRing (StateMatrix n) := CStarMatrix.instNormedRing

noncomputable instance (n : ℕ) : NormedAlgebra ℂ (StateMatrix n) := by
{
  unfold StateMatrix
  exact CStarMatrix.instNormedAlgebra (n := Fin n) (A := ℂ)
}



/--
noncomputable instance (n : ℕ) : NormedAlgebra ℂ (StateMatrix n) := CStarMatrix.instNormedAlgebra

Gives the following error:
type mismatch
  CStarMatrix.instNormedAlgebra
has type
  @NormedAlgebra ℂ (CStarMatrix ?m.3869 ?m.3869 ?m.3865) Complex.instNormedField
    (@NormedRing.toSeminormedRing (CStarMatrix ?m.3869 ?m.3869 ?m.3865)
      CStarMatrix.instNormedRing) : Type (max ?u.3864 ?u.3863)
but is expected to have type
  @NormedAlgebra ℂ (StateMatrix n) Complex.instNormedField
    (@NormedRing.toSeminormedRing (StateMatrix n) (instNormedRingStateMatrix n)) : Type
-/


structure DiscreteLinearSystemState (n p : ℕ) where
  a : StateMatrix n             -- State transition matrix (n×n)
  B : InputMatrix n p           -- Input matrix (n×p)
  x₀ : StateVector n            -- Initial state
  x : ℕ → StateVector n         -- State sequence
  u : ℕ → InputVector p         -- Input sequence

-- System evolution function
noncomputable def system_evolution {n p : ℕ} (sys : DiscreteLinearSystemState n p) : ℕ → StateVector n
  | 0 => sys.x₀
  | k + 1 => sys.a.mulVec (system_evolution sys k) + sys.B.mulVec (sys.u k)

-- State system equation
def state_system_equation {n p : ℕ} (sys : DiscreteLinearSystemState n p) : Prop :=
  ∀ k : ℕ, sys.x (k + 1) = sys.a.mulVec (sys.x k) + sys.B.mulVec (sys.u k)

-- Now you can use properties that require NormedRing/NormedAlgebra
def system_is_stable {n p : ℕ} (sys : DiscreteLinearSystemState n p) : Prop :=
  spectral_radius_less_than_one3 sys.a
