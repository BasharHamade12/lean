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
import Mathlib.Order.LiminfLimsup


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



noncomputable instance (n : ℕ) : Ring (StateMatrix n) := CStarMatrix.instRing


-- noncomputable instance (n : ℕ) : SeminormedAddCommGroup (StateMatrix n) := Matrix.seminormedAddCommGroup


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

def zero_input {p : ℕ} : ℕ → InputVector p := fun _ => 0


lemma system_power_multiplication {n : ℕ} (a : StateMatrix n ) (k : ℕ) :
  a ^ (k + 1) = a * (a ^ k) := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    rw [pow_succ]
    rw [ih]
    rw [mul_assoc ,<-pow_succ,ih]

lemma state_evolution_zero_input {n p : ℕ} (sys : DiscreteLinearSystemState n p)
  (h_init : sys.x 0 = sys.x₀)
  (h_state : state_system_equation sys)
  (h_zero_input : sys.u = zero_input) :
  ∀ k, sys.x k = (sys.a ^ k).mulVec sys.x₀ := by
  intro k
  induction' k with k ih
  ·
    simp
    trivial

  · rw [state_system_equation] at h_state
    specialize h_state k
    rw [ih] at h_state
    simp at h_state
    rw [h_zero_input] at h_state
    unfold zero_input at h_state
    simp at h_state
    rw [h_state]
    have h_A : sys.a ^ (k + 1) = sys.a * (sys.a ^ k) := by
      rw [system_power_multiplication]

    rewrite [h_A]
    rfl
example [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] (a : A)
  (h : spectral_radius_less_than_one3 a) :
  Filter.limsup (fun (n : ℕ) => (‖a ^ n‖₊ : ENNReal) ^ (1 / n : ℝ)) Filter.atTop < 1 :=
  gelfand_le_one_when_spectral_radius_le_one a h

theorem convergence
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    (a : A)
    (h : Filter.limsup (fun n : ℕ ↦ (‖a ^ n‖₊ : ENNReal)) Filter.atTop < 1) :
    ∃ (r : ENNReal) (N : ℕ), 0 < r ∧ r < 1 ∧ ∀ (k : ℕ), N < k → (‖a ^ k‖₊ : ENNReal) < r := by


  obtain ⟨r, h_limsup_lt_r, h_r_lt_one⟩ := exists_between h

  have r_pos : 0 < r := lt_of_le_of_lt (zero_le _) h_limsup_lt_r



  have eventually_lt := Filter.eventually_lt_of_limsup_lt h_limsup_lt_r


  rw [Filter.eventually_atTop] at eventually_lt
  obtain ⟨N, hN⟩ := eventually_lt

  use r, N
  refine ⟨r_pos, h_r_lt_one, fun k hk => hN k (Nat.le_of_lt hk)⟩

theorem gelfand_eventually_bounded {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    (a : A) (h : Filter.limsup (fun n : ℕ ↦ (‖a ^ n‖₊ : ENNReal) ^ (1 / n : ℝ)) Filter.atTop < 1) :
    ∃ (r : ENNReal) (N : ℕ), 0 < r ∧ r < 1 ∧ ∀ (k : ℕ), N < k → (‖a ^ k‖₊ : ENNReal) ^ (1 / k : ℝ) < r :=
by
  obtain ⟨r, h_limsup_lt_r, h_r_lt_one⟩ := exists_between h
  have r_pos : 0 < r := lt_of_le_of_lt (zero_le _) h_limsup_lt_r

  have eventually_lt := Filter.eventually_lt_of_limsup_lt h_limsup_lt_r

  rw [Filter.eventually_atTop] at eventually_lt
  obtain ⟨N, hN⟩ := eventually_lt

  use r, N
  refine ⟨r_pos, h_r_lt_one, fun k hk => hN k (Nat.le_of_lt hk)⟩



theorem asymptotic_stability_discrete [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] {n p : ℕ} (sys : DiscreteLinearSystemState n p)
  (h_init : sys.x 0 = sys.x₀)
  (h_state : state_system_equation sys)
  (h_zero_input : sys.u = zero_input)
  (h_spectral : spectral_radius_less_than_one3 sys.a) :
  Filter.Tendsto (fun k => ‖sys.x k‖) Filter.atTop (nhds 0) := by
    unfold Filter.Tendsto


    have hx : ∀ k, sys.x k = (sys.a ^ k).mulVec sys.x₀ :=
      state_evolution_zero_input sys h_init h_state h_zero_input

    have h_gelfand := spectrum.limsup_pow_nnnorm_pow_one_div_le_spectralRadius sys.a
    simp only [hx]
    have h_gelfand_le_one : Filter.limsup (fun (n : ℕ) => (‖sys.a ^ n‖₊ : ENNReal) ^ (1 / n : ℝ)) Filter.atTop < 1 := by
      unfold spectral_radius_less_than_one3 at h_spectral
      refine lt_of_le_of_lt ?_ h_spectral
      exact h_gelfand

    have eventually_bounded := gelfand_eventually_bounded sys.a h_gelfand_le_one
    obtain ⟨r, N, r_pos, r_lt_one, h_bound⟩ := eventually_bounded

    have h_power : ∀ (k : ℕ), N < k → ↑‖sys.a ^ k‖₊ < r ^ k := by
      intros k' hk'
      specialize h_bound k' hk'
      have h_k'_pos : 0 < k' := Nat.zero_lt_of_lt hk'
      have h_inv_k' : (k' : ℝ)⁻¹ * k' = 1 := by
        field_simp


      -- Take k'-th power of both sides
      have h_pow : (↑‖sys.a ^ k'‖₊ ^ (1 / k' : ℝ)) ^ k' < r ^ k' := by
        simp

        sorry

      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul] at h_pow
      simp at h_pow
      rw [h_inv_k'] at h_pow
      simp at h_pow
      exact h_pow


    sorry
