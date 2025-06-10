--import Init.Data.Nat.Div.Basic

def gcd (m n : Nat) : Nat := if m = 0 then n else gcd (n % m) m
  termination_by m
  decreasing_by simp_wf; apply Nat.mod_lt _ (Nat.zero_lt_of_ne_zero _); assumption

def gcd_simple (m n : Nat) : Nat := if m = 0 then n else gcd_simple (n % m) m
termination_by m
decreasing_by
  have h_not_zero : ¬m = 0 := by assumption
  apply Nat.mod_lt
  replace h_not_zero : m ≠ 0 := h_not_zero
  apply Nat.zero_lt_of_ne_zero
  exact h_not_zero
