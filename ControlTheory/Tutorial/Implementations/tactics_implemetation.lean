



theorem  rfl_example (a : Nat) : a = a  := by
  rfl

theorem  rw_example (a : Nat) : a + b = b + a  := by
  rw [Nat.add_comm]
  -- uses the commutative property of addition to rewrite a + b as b + a

def exact_example (f : A -> B ) (a : A) : B  := by
  exact (f a)


def apply_example (f : A -> B -> C ) (g : A -> B) (a : A) : C  := by
   apply f
   . exact a
   . apply g  -- or simply exact (g a)
     exact a

theorem cases_example  : forall a b c : Bool , a = b ∨ b = c ∨ a = c  := by

  intros a b c
  cases a with
  | true =>
    cases b with
    | true => exact Or.inl rfl
    | false => cases  c with
      | true =>
          apply Or.inr
          apply Or.inr
          rfl
      | false =>
          apply Or.inr
          apply Or.inl
          rfl

  | false =>
    cases b with
    | false =>

        apply Or.inl
        rfl
    | true => cases c with
      | true =>
          apply Or.inr
          apply Or.inl
          rfl
      | false =>
          apply Or.inr
          apply Or.inr
          rfl
