--import Mathlib

open scoped ComplexOrder

variable {σ ι : Type*}
variable [NormedAddCommGroup σ] [NormedSpace ℂ σ]
variable [NormedAddCommGroup ι] [NormedSpace ℂ ι]

variable (σ ι) in
structure DiscreteLinearSystemState where
  /-- State transition matrix (n×n) -/
  a : σ →L[ℂ] σ
  /-- Input matrix (n×p) -/
  B : ι →L[ℂ] σ
  /-- Initial state -/
  x₀ : σ
  /-- State sequence -/
  x : ℕ → σ
  /-- Input sequence -/
  u : ℕ → ι

-- System evolution function
noncomputable def system_evolution (sys : DiscreteLinearSystemState σ ι) : ℕ → σ
  | 0 => sys.x₀
  | k + 1 => sys.a (system_evolution sys k) + sys.B (sys.u k)

-- Definition: Assumption that the system's state sequence satisfies the evolution equation
def state_system_equation (sys : DiscreteLinearSystemState σ ι) : Prop :=
  ∀ k : ℕ, sys.x (k + 1) = sys.a (sys.x k) + sys.B (sys.u k)

-- Zero input sequence
def zero_input : ℕ → ι := fun _ => 0

-- Lemma: Power multiplication for continuous linear maps
lemma system_power_multiplication (a : σ →L[ℂ] σ) (k : ℕ) :
    a ^ (k + 1) = (a ^ k).comp a := by
  induction k with
  | zero =>
    simp [pow_zero]
    exact ContinuousLinearMap.id_comp a

  | succ k ih =>
    rw [pow_succ]
    rw [ih]
    rfl

lemma system_power_multiplication_flopped (a : σ →L[ℂ] σ) (k : ℕ) :
    a ^ (k + 1) = a.comp (a^k) := by
  induction k with
  | zero =>
    simp [pow_zero]
    exact ContinuousLinearMap.id_comp a

  | succ k ih =>
    rw [pow_succ]
    rw [ih]
    -- Now we have: a.comp (a^k) * a = a.comp (a^(k + 1))
    -- Since * is composition, this is: (a.comp (a^k)).comp a = a.comp (a^(k + 1))
    -- And by IH, a^(k + 1) = a.comp (a^k), so we need:
    -- (a.comp (a^k)).comp a = a.comp (a.comp (a^k))
    simp only [←ContinuousLinearMap.mul_def]
    rw [mul_assoc]
    -- Now we need: a * (a ^ k * a) = a * (a * a ^ k)
    congr 1


-- Lemma: State evolution under zero input
-- Lemma: State evolution under zero input
lemma state_evolution_zero_input (sys : DiscreteLinearSystemState σ ι)
    (h_init : sys.x 0 = sys.x₀)
    (h_state : state_system_equation sys)
    (h_zero_input : sys.u = zero_input) :
    ∀ k, sys.x k = (sys.a ^ k) sys.x₀ := by
  intro k
  induction' k with k ih
  · simp [pow_zero, h_init]
  · have h1 : sys.x (k + 1) = sys.a (sys.x k) + sys.B (sys.u k) := h_state k
    rw [ih] at h1
    rw [h_zero_input] at h1
    unfold zero_input at h1
    simp [ContinuousLinearMap.map_zero] at h1
    rw [h1]
    -- Now we need to show: sys.a ((sys.a ^ k) sys.x₀) = (sys.a ^ (k + 1)) sys.x₀
    rw [←ContinuousLinearMap.comp_apply]
    congr 1

    rw [system_power_multiplication_flopped]


    -- Now we need to show: sys.a.comp (sys.a ^ k) = sys.a ^ (k + 1)






-- Original theorem: Bound on state norm
theorem bound_x_norm
    (sys : DiscreteLinearSystemState σ ι)
    (hx : ∀ k, sys.x k = (sys.a ^ k) sys.x₀) (N : ℕ) :
    ∀ k, N < k → ‖sys.x k‖ ≤ ‖sys.a ^ k‖ * ‖sys.x₀‖ := by
  intro k hk
  -- Use the assumption hx to rewrite sys.x k
  rw [hx k]
  exact ContinuousLinearMap.le_opNorm (sys.a ^ k) sys.x₀

-- Definition: Spectral radius less than one
def spectral_radius_less_than_one (a : σ →L[ℂ] σ) : Prop :=
  spectralRadius ℂ a < 1

-- Theorem: Gelfand's formula application
theorem gelfand_le_one_when_spectral_radius_le_one
    [CompleteSpace σ] (a : σ →L[ℂ] σ) :
    spectral_radius_less_than_one a →
    Filter.limsup (fun (n : ℕ) => (‖a ^ n‖₊ : ENNReal) ^ (1 / n : ℝ)) Filter.atTop < 1 := by
  intro h_spectral
  unfold spectral_radius_less_than_one at h_spectral
  have h_gelfand := spectrum.limsup_pow_nnnorm_pow_one_div_le_spectralRadius a
  convert lt_of_le_of_lt h_gelfand h_spectral
