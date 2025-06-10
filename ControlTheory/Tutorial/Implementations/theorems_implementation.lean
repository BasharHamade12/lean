def isEven (n : Nat) : Prop := n % 2 = 0



theorem two_is_even : isEven 2 := by
  unfold isEven
  simp



example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=

  fun h : ∀ x : α, p x ∧ q x =>
  fun y : α =>
  show p y from (h y).left
