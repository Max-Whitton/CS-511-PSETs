-- Second assignment

import Mathlib.Data.Real.Basic
import Library.Basic


-- Example 3
example (h1 : A ∨ B) (h2 : A → C) (h3 : B → D) : C ∨ D := by
  cases h1
  · apply Or.inl
    apply h2
    assumption
  · apply Or.inr
    apply h3
    assumption



--Exercise 4
section
open Classical
variable {A B C : Prop}

example (h : ¬ B → ¬ A) : A → B := by
  intro a
  apply byContradiction
  intro nb
  have na : ¬ A := h nb
  apply na
  contradiction



example (h : A → B) : ¬ A ∨ B := by
  apply byContradiction
  intro h'
  apply h'
  apply Or.inr
  apply h
  apply byContradiction
  intro na
  apply h'
  apply Or.inl
  apply na


end



-- Problem 2.1
example (a b : ℝ) (h : a ≤ b) : a ^ 3 ≤ b ^ 3 := by
  have h1 :=
  calc
    0  = b-b := by ring
    _ ≤ b - a := by rel[h]
  have h2: (b+a)^2 ≥ 0 := by extra
  have h3: (b-a)^2 ≥ 0 := by extra
  have h4 :=
  calc
    0 = 0*(0 + 3*(0)) / 4 := by ring
    _ ≤ 0*((0) + 3*(b+a)^2) / 4 := by rel[h2]
    _ ≤ 0*((b-a)^2 + 3*(b+a)^2) / 4 := by rel[h3]
    _ ≤ ((b-a)*((b-a)^2 + 3*(b+a)^2) )/ 4 := by rel[h1]
  have h5 : (b ^ 3) = (a^3 + ((b-a)*((b-a)^2 + 3*(b+a)^2) / 4 )) := by ring
  calc
    a ^3 = a^3 + (0) := by ring
    _  ≤ (a^3 + ((b-a)*((b-a)^2 + 3*(b+a)^2) / 4 )) := by rel[h4]
    _ ≤  (b^3) := by rw[h5]


-- Problem 2.2
example {n : ℤ} (hn : n ^ 2 + 4 = 4 * n) : n = 2 := by
  have h1 :=
  calc
    0 = - (4*n) + (4 * n) := by ring
    _ = - (4 * n) + (n ^ 2 + 4) := by rw[hn]
    _ =  (n-2) ^ 2 := by ring
  have h2 :=
  calc
    (0 ^2)  = (0) := by ring
    _ = (n-2) ^ 2 := by rw[h1]
  have h3 :=
  calc
    (n-2)^2 = ((n-2)^2) := by ring
    _ = 0 := by rw[h1]
    _ = 0 ^ 2 := by ring
  have h4 : (n-2) = 0 := by cancel 2 at h3
  calc
    n = (n-2) + 2 := by ring
    _ =  0 + 2 := by rw[h4]
    _ = 2 := by ring





-- Problem 2.3
example {s : ℚ} (h1 : 3 * s ≤ -6) (h2 : 2 * s ≥ -4) : s = -2 := by
  apply le_antisymm
  calc
    s = (3 * s) / 3 := by ring
    _ ≤ (-6) / 3 := by rel[h1]
    _ = (-2) := by ring
  calc
    s = (2*s) /2 := by ring
    _ ≥ (-4) /2 := by rel[h2]
    _ = -2 := by ring
