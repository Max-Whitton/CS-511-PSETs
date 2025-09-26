-- Third assignment

import Mathlib.Data.Real.Basic
import Library.Basic

section
open Classical
variable (A B : Prop)


-- Exercise 3
theorem dne (h : ¬ ¬ P) : P :=
  byContradiction fun hnp : ¬P =>
    show False from h hnp

example : ¬ (¬ A ∨ B) → A :=
fun hL : ¬ (¬ A ∨ B) ↦
show A from dne
  (show (¬ ¬ A)  from (And.left
    (show ((¬¬A) ∧ ¬ B) from ((not_or).mp hL))))

example : (¬ P ∧ ¬ Q) →  ¬(P ∨ Q) :=
fun hL : ¬ P ∧ ¬ Q ↦
show ¬(P ∨ Q) from fun pvq : P ∨ Q =>
show False from
match pvq with
  | Or.inl P => And.left hL P
  | Or.inr Q => And.right hL Q

end

-- Exercise 2.3.6.2
example {x : ℝ} (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 := by
  match h with
    | Or.inl one =>
      have hr :=
        calc
          0 = 1*1 - (3*1) + 2 := by ring
          _ = x*x - 3*x + 2 := by rw[one]
          _ = x^2 - 3 * x +2 := by ring
      calc
        x ^ 2 - 3 * x + 2 = 0 := by rw[hr]
    | Or.inr two =>
      have hr :=
        calc
          0 = 2*2 - (3*2) + 2 := by ring
          _ = x*x - 3*x + 2 := by rw[two]
          _ = x^2 - 3 * x +2 := by ring
      calc
        x ^ 2 - 3 * x + 2 = 0 := by rw[hr]

-- Exercise 2.3.6.3
example {t : ℚ} (h : t = -2 ∨ t = 3) : t ^ 2 - t - 6 = 0 := by
  match h with
    | Or.inl ntwo =>
      have hr :=
        calc
          0 = (-2) ^ 2 - (-2) - 6 := by ring
          _ = t ^ 2 - t - 6 := by rw[ntwo]
      calc
        t ^ 2 - t - 6 = 0 := by rw[hr]
    | Or.inr three =>
      have hr :=
        calc
          0 = (3) ^ 2 - (3) - 6 := by ring
          _ = t ^ 2 - t - 6 := by rw[three]
      calc
        t ^ 2 - t - 6 = 0 := by rw[hr]

-- Exercise 2.3.6.4
example {x y : ℝ} (h : x = 2 ∨ y = -2) : x * y + 2 * x = 2 * y + 4 := by
  cases h with
  | inl hx =>
    rw [hx]
    ring
  | inr hy =>
    rw [hy]
    ring


-- Problem 2
example (n : ℕ) : Even n ∨ Odd n := by
  simple_induction n with k IH
  ·
    left
    use 0
    numbers
  ·
    obtain ⟨x, heven⟩ | ⟨x, hodd⟩ := IH
    ·
      right
      use x
      calc
        k + 1 = (x+x) + 1 := by rw[heven]
        _ = 2*x + 1 := by ring
    ·
      left
      use (x + 1)
      rw[hodd]
      ring
