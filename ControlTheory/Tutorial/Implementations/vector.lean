import Mathlib.Init
import Lean.Elab.Tactic.Rewrite
import Mathlib.Tactic

inductive Vector2 (α : Type) : Nat → Type
  | nil : Vector2 α 0
  | cons : α → Vector2 α n → Vector2 α (n + 1)

def append {α : Type} {m n : Nat} : Vector2 α m → Vector2 α n → Vector2 α (m + n)
  | Vector2.nil, ys => by
    rw [Nat.zero_add]
    exact ys
  | Vector2.cons x xs, ys => by
    rw [Nat.add_assoc]
    nth_rw 2 [Nat.add_comm]
    exact Vector2.cons x (append xs ys)
