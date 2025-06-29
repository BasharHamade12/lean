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


open Matrix Finset

variable {R : Type*} [NormedField R]
variable {n : ℕ}


noncomputable instance : NormedSpace R (Fin n → Fin n → R) :=
  Matrix.normedSpace

-- Define state and input vector types
def StateVector (n : ℕ) := Fin n → ℝ
def InputVector (p : ℕ) := Fin p → ℝ

-- Add Zero instances
instance {n : ℕ} : Zero (StateVector n) := ⟨fun _ => 0⟩
instance {p : ℕ} : Zero (InputVector p) := ⟨fun _ => 0⟩



instance {n : ℕ} : NormedAddCommGroup (StateVector n) :=
  Pi.normedAddCommGroup  -- This gives us the standard normed space structure

instance {n : ℕ} : MetricSpace (StateVector n) :=
  NormedAddCommGroup.toMetricSpace  -- This gives us the metric space structure

-- Add Norm instance
noncomputable instance {n : ℕ} : Norm (StateVector n) where
  norm x := Real.sqrt (∑ i, (x i)^2)

structure DiscreteLinearSystemState (n p : ℕ) where
  A : Matrix (Fin n) (Fin n) ℝ  -- State transition matrix (n×n)
  B : Matrix (Fin n) (Fin p) ℝ  -- Input matrix (n×p)
  x₀ : StateVector n            -- initial state sequence
  x : ℕ → StateVector n         -- State sequence
  u : ℕ → InputVector p         -- Input sequence

-- System evolution function
def system_evolution {n p : ℕ} (sys : DiscreteLinearSystemState n p) : ℕ → StateVector n
  | 0 => sys.x₀
  | k + 1 => sys.A.mulVec (system_evolution sys k) + sys.B.mulVec (sys.u k)

def state_system_equation {n p : ℕ} (sys : DiscreteLinearSystemState n p) : Prop :=
  ∀ k : ℕ, sys.x (k + 1) = sys.A.mulVec (sys.x k) + sys.B.mulVec (sys.u k)

def OutputVector (q : ℕ) := Fin q → ℝ

structure DiscreteLinearSystemOutput (n p q : ℕ) where
  C : Matrix (Fin q) (Fin n) ℝ  -- Output matrix (q×n)
  D : Matrix (Fin q) (Fin p) ℝ  -- Feedthrough matrix (q×p)
  y : ℕ → OutputVector q        -- Output sequence
  u : ℕ → InputVector p         -- Input sequence
  x : ℕ → StateVector n         -- State sequence

def output_system_equation {n p q: ℕ} (sys : DiscreteLinearSystemOutput n p q) : Prop :=
  ∀ k : ℕ, sys.y k = sys.C.mulVec (sys.x k) + sys.D.mulVec (sys.u k)

-- Define zero input condition
def zero_input {p : ℕ} : ℕ → InputVector p := fun _ => 0

-- Define spectral radius condition (all eigenvalues have magnitude < 1)
--def spectral_radius_less_than_one {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  --∀ l : ℝ , l ∈ spectrum ℝ A → abs l < 1

def spectral_radius_less_than_one {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ z : ℂ, z ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)) → norm z < 1

def spectral_radius_less_than_one2 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  spectralRadius ℂ (A.map (algebraMap ℝ ℂ)) < 1


theorem norm_pow_one_div_lt_one_of_spectral_radius_lt_one (hA : spectralRadius ℂ A < 1) :
    ∃ N : ℕ, ∀ n ≥ N, (‖A ^ n‖₊ : ℝ) ^ (1 / n) < 1 := by
  -- Gelfand's formula: ‖A^n‖₊^(1/n) → ρ(A)
  have h_tendsto := spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius A
  -- Since ρ(A) < 1, there exists ε > 0 such that ρ(A) + ε < 1
  obtain ⟨ε, hε_pos, hε_lt⟩ := exists_pos_lt_sub hA zero_lt_one
  -- By convergence, ∃ N such that ∀ n ≥ N, ‖A^n‖₊^(1/n) < ρ(A) + ε
  rw [Metric.tendsto_atTop] at h_tendsto
  specialize h_tendsto ε hε_pos
  obtain ⟨N, hN⟩ := h_tendsto
  -- Thus, for n ≥ N, ‖A^n‖₊^(1/n) < ρ(A) + ε < 1
  refine ⟨N, fun n hn => ?_⟩
  specialize hN n hn
  rw [dist_eq_norm] at hN
  simp at hN
  exact lt_trans hN hε_lt


lemma system_power_multiplication {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
  A ^ (k + 1) = A * (A ^ k) := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    rw [pow_succ]
    rw [ih]
    rw [mul_assoc ,<-pow_succ,ih]






-- Helper lemma: State evolution under zero input
lemma state_evolution_zero_input {n p : ℕ} (sys : DiscreteLinearSystemState n p)
  (h_init : sys.x 0 = sys.x₀)
  (h_state : state_system_equation sys)
  (h_zero_input : sys.u = zero_input) :
  ∀ k, sys.x k = (sys.A ^ k).mulVec sys.x₀ := by
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
    have h_A : sys.A ^ (k + 1) = sys.A * (sys.A ^ k) := by
      rw [system_power_multiplication]

    rewrite [h_A]
    rfl

theorem asymptotic_stability_discrete {n p : ℕ} (sys : DiscreteLinearSystemState n p)
  (h_init : sys.x 0 = sys.x₀)
  (h_state : state_system_equation sys)
  (h_zero_input : sys.u = zero_input)
  (h_spectral : spectral_radius_less_than_one2 sys.A) :
  Filter.Tendsto (fun k => ‖sys.x k‖) Filter.atTop (nhds 0) := by
  unfold Filter.Tendsto
    -- Express state vector in terms of matrix power
  have hx : ∀ k, sys.x k = (sys.A ^ k).mulVec sys.x₀ :=
    state_evolution_zero_input sys h_init h_state h_zero_input


  simp only [hx]
  --unfold Filter.Tendsto
  unfold spectral_radius_less_than_one2 at h_spectral





  sorry
