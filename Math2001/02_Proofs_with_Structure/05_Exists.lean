/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {a : ℚ} (h : ∃ b : ℚ, a = b ^ 2 + 1) : a > 0 := by
  obtain ⟨b, hb⟩ := h
  calc
    a = b ^ 2 + 1 := hb
    _ > 0 := by extra


example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  obtain ⟨x, hxt⟩ := h
  have H := le_or_gt x 0
  obtain hx | hx := H
  · have hxt' : 0 < (-x) * t := by addarith [hxt]
    have hx' : 0 ≤ -x := by addarith [hx]
    cancel -x at hxt'
    apply ne_of_gt
    apply hxt'
  · have hxt'' : 0 < x * (-t) :=
    calc 0 < (-x) * t := by addarith [hxt]
      _ = x * (-t) := by ring
    cancel x at hxt''
    have hxt''' : t < 0 := by addarith [hxt'']
    apply ne_of_lt
    apply hxt'''

example : ∃ n : ℤ, 12 * n = 84 := by
  use 7
  numbers


example (x : ℝ) : ∃ y : ℝ, y > x := by
  use x + 1
  extra


example : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 11 := by
  use 6, 5
  numbers

example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use a + 1, a
  ring

example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p + q) / 2
  constructor
  · calc p = (p + p) / 2 := by ring
    _ < (p + q) / 2 := by rel [h]
  · calc (p + q) / 2 < (q + q) / 2 := by rel [h]
    _ = q := by ring

example : ∃ a b c d : ℕ,
    a ^ 3 + b ^ 3 = 1729 ∧ c ^ 3 + d ^ 3 = 1729 ∧ a ≠ c ∧ a ≠ d := by
  use 1, 12, 9, 10
  constructor
  numbers
  constructor
  numbers
  constructor
  numbers
  numbers

/-! # Exercises -/


example : ∃ t : ℚ, t ^ 2 = 1.69 := by
  use 13 / 10
  numbers
example : ∃ m n : ℤ, m ^ 2 + n ^ 2 = 85 := by
  use 6, 7
  numbers

example : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by
  use -1 / 2
  constructor
  · numbers
  · numbers
example : ∃ a b : ℕ, 2 ^ a = 5 * b + 1 := by
  use 0, 0
  numbers

example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  use x + 1 / 2
  have h1 : (x + 1 / 2) ^ 2 = x ^ 2 + x + 1 / 4 := by ring
  have h2 : x ^ 2 + x + 1 / 4 ≥ x + 1 / 4 := by extra
  rw [h1]
  addarith [h2]

/-
example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  obtain ⟨x, hxt⟩ := h
  have hxt1 : (1 - x) * (t - 1) = -x * t + t + x - 1 := by ring
  have hxt2 : (x - 1) * -(t - 1) = (1 - x) * (t - 1) := by ring
  have hxt3 : (1 - x) * (t - 1) > 0
  · rw [hxt1]
    addarith [hxt]
  have hxt4 : (x - 1) * -(t - 1) > 0
  · rw [hxt2]
    apply hxt3
  obtain hx1 | hx2 : x - 1 ≤ 0 ∨ x - 1 > 0 := le_or_gt (x - 1) 0
  · have hx3 : 1 - x ≥ 0 := by addarith [hx1]
    cancel 1 - x at hxt3
    apply ne_of_gt
    addarith [hxt3]
  · cancel x - 1 at hxt4
    apply ne_of_lt
    addarith [hxt4]
-/

example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  obtain ⟨x, hxt⟩ := h
  have hxt1 : -x * t + t + x - 1 = (1 - x) * (t - 1) := by ring
  have hxt2 : (1 - x) * (t - 1) = (x - 1) * -(t - 1) := by ring
  have hxt3 : -x * t + t + x - 1 > 0 := by addarith [hxt]
  rw [hxt1] at hxt3
  obtain hx1 | hx2 : x - 1 ≤ 0 ∨ x - 1 > 0 := le_or_gt (x - 1) 0
  · have hx3 : 1 - x ≥ 0 := by addarith [hx1]
    cancel 1 - x at hxt3
    apply ne_of_gt
    addarith [hxt3]
  · rw [hxt2] at hxt3
    cancel x - 1 at hxt3
    apply ne_of_lt
    addarith [hxt3]

example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  obtain ⟨x, hxm⟩ := h
  obtain hx1 | hx2 : x ≤ 2 ∨ 3 ≤ x := le_or_succ_le x 2
  · have hx3 : 2 * x ≤ 2 * 2 := by rel [hx1]
    apply ne_of_lt
    addarith [hxm, hx3]
  · have hx4 : 2 * 3 ≤ 2 * x := by rel [hx2]
    apply ne_of_gt
    addarith [hxm, hx4]

example {n : ℤ} : ∃ a, 2 * a ^ 3 ≥ n * a + 7 := by
  obtain hn1 | hn2 : n ≤ 2 ∨ n > 2 := le_or_gt n 2
  · use 2
    have hn3 : 2 * 2 + 7 ≥ n * 2 + 7 := by rel [hn1]
    addarith [hn3]
  · use n
    have hn4 : 2 * n ^ 3 = n ^ 3 + (n - 1) * n ^ 2 + n * n := by ring
    have hn5 : n ^ 3 + (n - 1) * n ^ 2 > 2 ^ 3 + (2 - 1) * 2 ^ 2 := by rel [hn2]
    rw [hn4]
    addarith [hn5]

example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by
  use (b + c - a) / 2, (a + c - b) / 2, (a + b - c) / 2
  constructor
  · addarith [ha]
  · constructor
    · addarith [hb]
    · constructor
      · addarith [hc]
      · constructor
        · ring
        · constructor
          · ring
          · ring
