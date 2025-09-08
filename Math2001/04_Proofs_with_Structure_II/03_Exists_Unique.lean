/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Theory.ModEq.Defs

math2001_init

namespace Int


example : ∃! a : ℝ, 3 * a + 1 = 7 := by
  use 2
  dsimp
  constructor
  · numbers
  intro y hy
  calc
    y = (3 * y + 1 - 1) / 3 := by ring
    _ = (7 - 1) / 3 := by rw [hy]
    _ = 2 := by numbers


/-
example : ∃! x : ℚ, ∀ a, a ≥ 1 → a ≤ 3 → (a - x) ^ 2 ≤ 1 := by
  use 2
  constructor
  · intro a ha1 ha2
    obtain ⟨ha3, ha4⟩ : -1 ≤ a - 2 ∧ a - 2 ≤ 1
    · constructor
      · addarith [ha1]
      · addarith [ha2]
    calc (a - 2) ^ 2 ≤ 1 ^ 2 := sq_le_sq' ha3 ha4 -- sq_le_sq' (by addarith [ha1]) (by addarith [ha2])
      _ = 1 := by numbers
  · intro y h1
    obtain ⟨h2, h3⟩ : (1:ℚ) ≥ 1 ∧ (1:ℚ) ≤ 3
    · constructor
      · numbers
      · numbers
    have h4 : (1 - y) ^ 2 ≤ 1 := by apply h1 1 h2 h3
    obtain ⟨h5, h6⟩ : (3:ℚ) ≥ 1 ∧ (3:ℚ) ≤ 3
    · constructor
      · numbers
      · numbers
    have h7 : (3 - y) ^ 2 ≤ 1 := by apply h1 3 h5 h6
    have h8 : (y - 2) ^ 2 ≤ 0 :=
    calc (y - 2) ^ 2 = ((1 - y) ^ 2 + (3 - y) ^ 2 - 2) / 2 := by ring
      _ ≤ (1 + 1 - 2) / 2 := by rel [h4, h7]
      _ = 0 := by numbers
    have h9 : (y - 2) ^ 2 ≥ 0 := by extra
    have h10 : (y - 2) ^ 2 = 0 := le_antisymm h8 h9
    cancel 2 at h10
    addarith [h10]
-/

example : ∃! x : ℚ, ∀ a, a ≥ 1 → a ≤ 3 → (a - x) ^ 2 ≤ 1 := by
  use 2
  constructor
  · intro a ha1 ha2
    obtain ⟨ha3, ha4⟩ : -1 ≤ a - 2 ∧ a - 2 ≤ 1 -- := by constructor <;> or constructor ; ;
    · constructor
      · addarith [ha1]
      · addarith [ha2]
    calc (a - 2) ^ 2 ≤ 1 ^ 2 := sq_le_sq' ha3 ha4
      _ = 1 := by numbers
  · intro y h1
    obtain ⟨h2, h3⟩ : (1 - y) ^ 2 ≤ 1 ∧ (3 - y) ^ 2 ≤ 1
    · constructor
      · apply h1
        · numbers
        · numbers
      · apply h1
        · numbers
        · numbers
    have h4 : (y - 2) ^ 2 ≤ 0 :=
    calc (y - 2) ^ 2 = ((1 - y) ^ 2 + (3 - y) ^ 2 - 2) / 2 := by ring
      _ ≤ (1 + 1 - 2) / 2 := by rel [h2, h3]
      _ = 0 := by numbers
    have h5 : (y - 2) ^ 2 ≥ 0 := by extra
    have h6 : (y - 2) ^ 2 = 0 := le_antisymm h4 h5
    cancel 2 at h6
    addarith [h6]

example {x : ℚ} (hx : ∃! a : ℚ, a ^ 2 = x) : x = 0 := by
  obtain ⟨a, ha1, ha2⟩ := hx
  have h1 : -a = a
  · apply ha2
    calc
      (-a) ^ 2 = a ^ 2 := by ring
      _ = x := ha1
  have h2 :=
    calc
      a = (a - -a) / 2 := by ring
      _ = (a - a) / 2 := by rw [h1]
      _ = 0 := by ring
  calc
    x = a ^ 2 := by rw [ha1]
    _ = 0 ^ 2 := by rw [h2]
    _ = 0 := by ring


example : ∃! r : ℤ, 0 ≤ r ∧ r < 5 ∧ 14 ≡ r [ZMOD 5] := by
  use 4
  dsimp
  constructor
  · constructor
    · numbers
    constructor
    · numbers
    use 2
    numbers
  intro r hr
  obtain ⟨hr1, hr2, q, hr3⟩ := hr
  have :=
    calc
      5 * 1 < 14 - r := by addarith [hr2]
      _ = 5 * q := by rw [hr3]
  cancel 5 at this
  have :=
    calc
      5 * q = 14 - r := by rw [hr3]
      _ < 5 * 3 := by addarith [hr1]
  cancel 5 at this
  interval_cases q
  addarith [hr3]

/-! # Exercises -/


example : ∃! x : ℚ, 4 * x - 3 = 9 := by
  use 3
  constructor
  · numbers
  · intro y h
    have : 4 * y = 4 * 3 := by addarith [h]
    cancel 4 at this

example : ∃! n : ℕ, ∀ a, n ≤ a := by
  use 0
  constructor
  · intro a
    extra
  · intro m h1
    have h2 : m ≤ 0 := by apply h1
    have h3 : 0 ≤ m := by extra
    apply le_antisymm h2 h3

example : ∃! r : ℤ, 0 ≤ r ∧ r < 3 ∧ 11 ≡ r [ZMOD 3] := by
  use 2
  constructor
  · constructor
    · numbers
    · constructor
      · numbers
      · use 3
        numbers
  · intro s h1
    obtain ⟨h2, h3, t, h4⟩ := h1
    have h5 : 11 - s < 3 * 4 := by addarith [h2]
    have h6 : 3 * 2 < 11 - s := by addarith [h3]
    rw [h4] at h5 h6
    cancel 3 at h5
    cancel 3 at h6
    interval_cases t
    addarith [h4]
