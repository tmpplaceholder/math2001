/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init

namespace Int


example {a : ℚ} : 3 * a + 1 ≤ 7 ↔ a ≤ 2 := by
  constructor
  · intro h
    calc a = ((3 * a + 1) - 1) / 3 := by ring
      _ ≤ (7 - 1) / 3 := by rel [h]
      _ = 2 := by numbers
  · intro h
    calc 3 * a + 1 ≤ 3 * 2 + 1 := by rel [h]
      _ = 7 := by numbers


example {n : ℤ} : 8 ∣ 5 * n ↔ 8 ∣ n := by
  constructor
  · intro hn
    obtain ⟨a, ha⟩ := hn
    use -3 * a + 2 * n
    calc
      n = -3 * (5 * n) + 16 * n := by ring
      _ = -3 * (8 * a) + 16 * n := by rw [ha]
      _ = 8 * (-3 * a + 2 * n) := by ring
  · intro hn
    obtain ⟨a, ha⟩ := hn
    use 5 * a
    calc 5 * n = 5 * (8 * a) := by rw [ha]
      _ = 8 * (5 * a) := by ring


theorem odd_iff_modEq (n : ℤ) : Odd n ↔ n ≡ 1 [ZMOD 2] := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    dsimp [Int.ModEq]
    dsimp [(· ∣ ·)]
    use k
    addarith [hk]
  · intro h'
    dsimp [Int.ModEq, (· ∣ ·)] at h'
    obtain ⟨j, hj⟩ := h'
    use j
    addarith [hj]

theorem even_iff_modEq (n : ℤ) : Even n ↔ n ≡ 0 [ZMOD 2] := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    dsimp [Int.ModEq]
    dsimp [(· ∣ ·)]
    use k
    addarith [hk]
  · intro h'
    obtain ⟨j, hj⟩ := h'
    use j
    addarith [hj]

example {x : ℝ} : x ^ 2 + x - 6 = 0 ↔ x = -3 ∨ x = 2 := by
  constructor
  · intro h1
    have h2 : (x + 3) * (x - 2) = 0 :=
    calc
      (x + 3) * (x - 2) = x ^ 2 + x - 6 := by ring
      _ = 0 := h1
    obtain h3 | h4 : x + 3 = 0 ∨ x - 2 = 0 := eq_zero_or_eq_zero_of_mul_eq_zero h2
    · left
      addarith [h3]
    · right
      addarith [h4]
  · intro h5
    obtain h6 | h7 := h5
    · calc
        x ^ 2 + x - 6 = (-3) ^ 2 + (-3) - 6 := by rw [h6]
        _ = 0 := by ring
    · calc
        x ^ 2 + x - 6 = 2 ^ 2 + 2 - 6 := by rw [h7]
        _ = 0 := by ring

example {a : ℤ} : a ^ 2 - 5 * a + 5 ≤ -1 ↔ a = 2 ∨ a = 3 := by
  constructor
  · intro h1
    have h2 : (2 * a - 5) ^ 2 ≤ 1 ^ 2 :=
    calc
      (2 * a - 5) ^ 2 = 4 * (a ^ 2 - 5 * a + 5) + 5 := by ring
      _ ≤ 4 * -1 + 5 := by rel [h1]
      _ = 1 ^ 2 := by numbers
    have h3 : 0 ≤ (1:ℤ) := by numbers
    obtain ⟨h4, h5⟩ := abs_le_of_sq_le_sq' h2 h3
    have h6 : 2 * 2 ≤ 2 * a := by addarith [h4]
    cancel 2 at h6
    have h7 : 2 * a ≤ 2 * 3 := by addarith [h5]
    cancel 2 at h7
    interval_cases a
    · left
      numbers
    · right
      numbers
  · intro h8
    obtain h9 | h10 := h8
    · calc
        a ^ 2 - 5 * a + 5 = 2 ^ 2 - 5 * 2 + 5 := by rw [h9]
        _ ≤ -1 := by numbers
    · calc
        a ^ 2 - 5 * a + 5 = 3 ^ 2 - 5 * 3 + 5 := by rw [h10]
        _ ≤ -1 := by numbers

example {n : ℤ} (hn : n ^ 2 - 10 * n + 24 = 0) : Even n := by
  have hn1 :=
    calc (n - 4) * (n - 6) = n ^ 2 - 10 * n + 24 := by ring
      _ = 0 := hn
  have hn2 := eq_zero_or_eq_zero_of_mul_eq_zero hn1
  obtain hn3 | hn4 := hn2
  · use 2
    addarith [hn3]
  · use 3
    addarith [hn4]

example {n : ℤ} (hn : n ^ 2 - 10 * n + 24 = 0) : Even n := by
  have hn1 :=
    calc (n - 4) * (n - 6) = n ^ 2 - 10 * n + 24 := by ring
      _ = 0 := hn
  rw [mul_eq_zero] at hn1 -- `hn1 : n - 4 = 0 ∨ n - 6 = 0`
  obtain hn2 | hn3 := hn1
  · use 2
    addarith [hn2]
  · use 3
    addarith [hn3]

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x + y + 1) := by
  rw [Int.odd_iff_modEq] at *
  calc x + y + 1 ≡ 1 + 1 + 1 [ZMOD 2] := by rel [hx, hy]
    _ = 2 * 1 + 1 := by ring
    _ ≡ 1 [ZMOD 2] := by extra


example (n : ℤ) : Even n ∨ Odd n := by
  mod_cases hn : n % 2
  · left
    rw [Int.even_iff_modEq]
    apply hn
  · right
    rw [Int.odd_iff_modEq]
    apply hn

/-! # Exercises -/


example {x : ℝ} : 2 * x - 1 = 11 ↔ x = 6 := by
  constructor
  · intro h1
    have h2 : 2 * x = 2 * 6 := by addarith [h1]
    cancel 2 at h2
  · intro h3
    rw [h3]
    numbers

example {n : ℤ} : 63 ∣ n ↔ 7 ∣ n ∧ 9 ∣ n := by
  constructor
  · intro h1
    constructor
    · obtain ⟨a, h2⟩ := h1
      use 9 * a
      rw [h2]
      ring
    · obtain ⟨b, h3⟩ := h1
      use 7 * b
      rw [h3]
      ring
  · intro h4
    obtain ⟨h5, h6⟩ := h4
    obtain ⟨c, h7⟩ := h5
    obtain ⟨d, h8⟩ := h6
    have h9 : n = 28 * n - 27 * n := by ring
    have h10 : 28 * n - 27 * n = 28 * n - 27 * (7 * c) := by rw [h7]
    rw [h9, h10, h8]
    use 4 * d - 3 * c
    ring

theorem dvd_iff_modEq {a n : ℤ} : n ∣ a ↔ a ≡ 0 [ZMOD n] := by
  constructor
  · intro h1
    have h2 : a = a - 0 := by ring
    rw [h2] at h1
    apply h1
  · intro h3
    have h4 : a = a - 0 := by ring
    rw [h4]
    apply h3

example {a b : ℤ} (hab : a ∣ b) : a ∣ 2 * b ^ 3 - b ^ 2 + 3 * b := by
  rw [dvd_iff_modEq] at *
  calc 2 * b ^ 3 - b ^ 2 + 3 * b ≡ 2 * 0 ^ 3 - 0 ^ 2 + 3 * 0 [ZMOD a] := by rel [hab]
    _ = 0 := by ring
    _ ≡ 0 [ZMOD a] := by extra

example {k : ℕ} : k ^ 2 ≤ 6 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by
  constructor
  · intro h1
    obtain h2 | h3 : k ≤ 2 ∨ 3 ≤ k := le_or_succ_le k 2
    · interval_cases k
      · left
        numbers
      · right
        left
        numbers
      · right
        right
        numbers
    · have h4 : 3 ^ 2 ≤ k ^ 2 := by rel [h3]
      interval_cases k ^ 2
  · intro h5
    obtain h6 | h7 | h8 := h5
    · rw [h6]
      numbers
    · rw [h7]
      numbers
    · rw [h8]
      numbers
