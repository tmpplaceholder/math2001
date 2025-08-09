/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {x y : ℝ} (h : x = 1 ∨ y = -1) : x * y + x = y + 1 := by
  obtain hx | hy := h
  calc
    x * y + x = 1 * y + 1 := by rw [hx]
    _ = y + 1 := by ring
  calc
    x * y + x = x * -1 + x := by rw [hy]
    _ = -1 + 1 := by ring
    _ = y + 1 := by rw [hy]

example {n : ℕ} : n ^ 2 ≠ 2 := by
  have hn := le_or_succ_le n 1
  obtain hn | hn := hn
  apply ne_of_lt
  calc
    n ^ 2 ≤ 1 ^ 2 := by rel [hn]
    _ < 2 := by numbers
  apply ne_of_gt
  calc
    2 < 2 ^ 2 := by numbers
    _ ≤ n ^ 2 := by rel [hn]

example {x : ℝ} (hx : 2 * x + 1 = 5) : x = 1 ∨ x = 2 := by
  right
  calc
    x = (2 * x + 1 - 1) / 2 := by ring
    _ = (5 - 1) / 2 := by rw [hx]
    _ = 2 := by numbers


example {x : ℝ} (hx : x ^ 2 - 3 * x + 2 = 0) : x = 1 ∨ x = 2 := by
  have h1 :=
    calc
    (x - 1) * (x - 2) = x ^ 2 - 3 * x + 2 := by ring
    _ = 0 := by rw [hx]
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  obtain h3|h4 := h2
  left
  addarith [h3]
  right
  addarith [h4]

example {n : ℤ} : n ^ 2 ≠ 2 := by
  have hn0 := le_or_succ_le n 0
  obtain hn0 | hn0 := hn0
  · have : 0 ≤ -n := by addarith [hn0]
    have hn := le_or_succ_le (-n) 1
    obtain hn | hn := hn
    · apply ne_of_lt
      calc
        n ^ 2 = (-n) ^ 2 := by ring
        _ ≤ 1 ^ 2 := by rel [hn]
        _ < 2 := by numbers
    · apply ne_of_gt
      calc
        (2:ℤ) < 2 ^ 2 := by numbers
        _ ≤ (-n) ^ 2 := by rel [hn]
        _ = n ^ 2 := by ring
  · have hn := le_or_succ_le n 1
    obtain hn | hn := hn
    · apply ne_of_lt
      calc
        n ^ 2 ≤ 1 ^ 2 := by rel [hn]
        _ < 2 := by numbers
    · apply ne_of_gt
      calc
        (2:ℤ) < 2 ^ 2 := by numbers
        _ ≤ n ^ 2 := by rel [hn]


/-! # Exercises -/


example {x : ℚ} (h : x = 4 ∨ x = -4) : x ^ 2 + 1 = 17 := by
  obtain h1 | h2 := h
  · rw [h1]
    numbers
  · rw [h2]
    numbers

example {x : ℝ} (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 := by
  obtain h1 | h2 := h
  · rw [h1]
    numbers
  · rw [h2]
    numbers

example {t : ℚ} (h : t = -2 ∨ t = 3) : t ^ 2 - t - 6 = 0 := by
  obtain h1 | h2 := h
  · rw [h1]
    numbers
  · rw [h2]
    numbers

example {x y : ℝ} (h : x = 2 ∨ y = -2) : x * y + 2 * x = 2 * y + 4 := by
  obtain h1 | h2 := h
  · rw [h1]
    ring
  · rw [h2]
    ring

example {s t : ℚ} (h : s = 3 - t) : s + t = 3 ∨ s + t = 5 := by
  left
  addarith [h]

example {a b : ℚ} (h : a + 2 * b < 0) : b < a / 2 ∨ b < - a / 2 := by
  right
  addarith [h]

example {x y : ℝ} (h : y = 2 * x + 1) : x < y / 2 ∨ x > y / 2 := by
  left
  addarith [h]

/-
example {x : ℝ} (hx : x ^ 2 + 2 * x - 3 = 0) : x = -3 ∨ x = 1 := by
  have hx1 : (x + 3) * (x - 1) - (x ^ 2 + 2 * x - 3) = 0 := by ring
  have hx2 : (x + 3) * (x - 1) - (x ^ 2 + 2 * x - 3) + (x ^ 2 + 2 * x - 3) = 0 + 0 := by rw [hx1, hx]
  have hx3 : (x + 3) * (x - 1) = 0 := by addarith [hx2]
  obtain h1 | h2 : x + 3 = 0 ∨ x - 1 = 0 := eq_zero_or_eq_zero_of_mul_eq_zero hx3
  · left
    addarith [h1]
  · right
    addarith [h2]
-/

example {x : ℝ} (hx : x ^ 2 + 2 * x - 3 = 0) : x = -3 ∨ x = 1 := by
  have hx1 : (x + 3) * (x - 1) = x ^ 2 + 2 * x - 3 := by ring
  rw [hx] at hx1
  obtain h1 | h2 : x + 3 = 0 ∨ x - 1 = 0 := eq_zero_or_eq_zero_of_mul_eq_zero hx1
  · left
    addarith [h1]
  · right
    addarith [h2]

example {a b : ℝ} (hab : a ^ 2 + 2 * b ^ 2 = 3 * a * b) : a = b ∨ a = 2 * b := by
  have hab1 : (a - b) * (a - 2 * b) - (a ^ 2 + 2 * b ^ 2 - 3 * a * b) = 0 := by ring
  have hab2 : (a - b) * (a - 2 * b) - (a ^ 2 + 2 * b ^ 2 - 3 * a * b) + (a ^ 2 + 2 * b ^ 2) = 0 + (3 * a * b) := by rw [hab1, hab]
  have hab3 : (a - b) * (a - 2 * b) = 0 := by addarith [hab2]
  obtain h1 | h2 : a - b = 0 ∨ a - 2 * b = 0 := eq_zero_or_eq_zero_of_mul_eq_zero hab3
  · left
    addarith [h1]
  · right
    addarith [h2]

example {t : ℝ} (ht : t ^ 3 = t ^ 2) : t = 1 ∨ t = 0 := by
  have ht1 : (t - 1) * (t ^ 2) - (t ^ 3 - t ^ 2) = 0 := by ring
  have ht2 : (t - 1) * (t ^ 2) - (t ^ 3 - t ^ 2) + t ^ 3 = 0 + t ^ 2 := by rw [ht1, ht]
  have ht3 : (t - 1) * (t ^ 2) = 0 := by addarith [ht2]
  obtain h1 | h2 : t - 1 = 0 ∨ t ^ 2 = 0 := eq_zero_or_eq_zero_of_mul_eq_zero ht3
  · left
    addarith [h1]
  · right
    cancel 2 at h2

example {n : ℕ} : n ^ 2 ≠ 7 := by
  obtain h1 | h2 : n ≤ 2 ∨ 3 ≤ n := le_or_succ_le n 2
  · apply ne_of_lt
    have h3 : n ^ 2 ≤ 2 ^ 2 := by rel [h1]
    addarith [h3]
  · apply ne_of_gt
    have h4 : 3 ^ 2 ≤ n ^ 2 := by rel [h2]
    addarith [h4]

example {x : ℤ} : 2 * x ≠ 3 := by
  obtain h1 | h2 : x ≤ 1 ∨ 2 ≤ x := le_or_succ_le x 1
  · apply ne_of_lt
    have h3 : 2 * x ≤ 2 * 1 := by rel [h1]
    addarith [h3]
  · apply ne_of_gt
    have h4 : 2 * 2 ≤ 2 * x := by rel [h2]
    addarith [h4]

example {t : ℤ} : 5 * t ≠ 18 := by
  obtain h1 | h2 : t ≤ 3 ∨ 4 ≤ t := le_or_succ_le t 3
  · apply ne_of_lt
    have h3 : 5 * t ≤ 5 * 3 := by rel [h1]
    addarith [h3]
  · apply ne_of_gt
    have h4 : 5 * 4 ≤ 5 * t := by rel [h2]
    addarith [h4]

example {m : ℕ} : m ^ 2 + 4 * m ≠ 46 := by
  obtain h1 | h2 : m ≤ 5 ∨ 6 ≤ m := le_or_succ_le m 5
  · apply ne_of_lt
    have h3 : m ^ 2 + 4 * m ≤ 5 ^ 2 + 4 * 5 := by rel [h1]
    addarith [h3]
  · apply ne_of_gt
    have h4 : 6 ^ 2 + 4 * 6 ≤ m ^ 2 + 4 * m := by rel [h2]
    addarith [h4]
