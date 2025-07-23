import Mathlib.ContinuousLinearMap

open scoped ComplexOrder

variable {σ ι : Type*}
variable [NormedAddCommGroup σ] [NormedSpace ℂ σ]
variable [NormedAddCommGroup ι] [NormedSpace ℂ ι]

variable (σ ι) in
structure DiscreteLinearSystemState  where
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

theorem bound_x_norm
    (sys : DiscreteLinearSystemState σ ι)
    (hx : ∀ k, sys.x k = (sys.a ^ k) sys.x₀) (N : ℕ) :
    ∀ k, N < k → ‖sys.x k‖ ≤ ‖sys.a ^ k‖ * ‖sys.x₀‖ := by
  intro k hk
  -- Use the assumption hx to rewrite sys.x k
  rw [hx k]
  exact ContinuousLinearMap.le_opNorm (sys.a ^ k) sys.x₀
