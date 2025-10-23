/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.ParityModular
import Library.Basic
import Library.Tactic.ModEq

math2001_init

open Int


example : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by
  intro h
  have : 0.5 ^ 2 ≥ 0.5 := h 0.5
  numbers at this


example : ¬ 3 ∣ 13 := by
  intro H
  obtain ⟨k, hk⟩ := H
  obtain h4 | h5 := le_or_succ_le k 4
  · have h :=
    calc 13 = 3 * k := hk
      _ ≤ 3 * 4 := by rel [h4]
    numbers at h
  · have h :=
    calc 13 = 3 * k := hk
      _ ≥ 3 * 5 := by rel [h5]
    numbers at h

example {x y : ℝ} (h : x + y = 0) : ¬(x > 0 ∧ y > 0) := by
  intro h
  obtain ⟨hx, hy⟩ := h
  have H :=
  calc 0 = x + y := by rw [h]
    _ > 0 := by extra
  numbers at H


example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  intro h1
  obtain ⟨n, h2⟩ := h1
  obtain h3 | h4 := le_or_succ_le n 1
  · have h5 : 2 ≤ 1 ^ 2 :=
    calc 2 = n ^ 2 := by rw [h2]
      _ ≤ 1 ^ 2 := by rel [h3]
    numbers at h5
  · have h6 : 2 ≥ 2 ^ 2 :=
    calc 2 = n ^ 2 := by rw [h2]
      _ ≥ 2 ^ 2 := by rel [h4]
    numbers at h6

example (n : ℤ) : Int.Even n ↔ ¬ Int.Odd n := by
  constructor
  · intro h1 h2
    rw [Int.even_iff_modEq] at h1
    rw [Int.odd_iff_modEq] at h2
    have h :=
    calc 0 ≡ n [ZMOD 2] := by rel [h1]
      _ ≡ 1 [ZMOD 2] := by rel [h2]
    numbers at h -- contradiction!
  · intro h
    obtain h1 | h2 := Int.even_or_odd n
    · apply h1
    · contradiction


example (n : ℤ) : Int.Odd n ↔ ¬ Int.Even n := by
  constructor
  · have h1 : Int.Odd n → Int.Even n → 0 ≡ 1 [ZMOD 2] <;> rw [Int.even_iff_modEq, Int.odd_iff_modEq] at * <;> intro h2 h3
    · calc 0 ≡ n [ZMOD 2] := by rel [h3]
        _ ≡ 1 [ZMOD 2] := by rel [h2]
    · have h4 : 0 ≡ 1 [ZMOD 2] := h1 h2 h3
      numbers at h4
  · obtain h5 | h6 := Int.even_or_odd n <;> intro h7
    · contradiction
    · apply h6

example (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 3]) := by
  intro h
  mod_cases hn : n % 3
  · have h :=
    calc (0:ℤ) = 0 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h -- contradiction!
  · have h :=
    calc (1:ℤ) = 1 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := h
    numbers at h
  · have h :=
    calc 1 ≡ 1 + 3 * 1 [ZMOD 3] := by extra
      _ = 2 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := h
    numbers at h

example {p : ℕ} (k l : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hkl : p = k * l) :
    ¬(Prime p) := by
  have hk : k ∣ p
  · use l
    apply hkl
  intro h
  obtain ⟨h2, hfact⟩ := h
  have : k = 1 ∨ k = p := hfact k hk
  obtain hk1' | hkp' := this
  · contradiction
  · contradiction


example (a b : ℤ) (h : ∃ q, b * q < a ∧ a < b * (q + 1)) : ¬b ∣ a := by
  intro H
  obtain ⟨k, hk⟩ := H
  obtain ⟨q, hq₁, hq₂⟩ := h
  have hb :=
  calc 0 = a - a := by ring
    _ < b * (q + 1) - b * q := by rel [hq₁, hq₂]
    _ = b := by ring
  have h1 :=
  calc b * k = a := by rw [hk]
    _ < b * (q + 1) := hq₂
  cancel b at h1
  have h2 : b * q < b * k := -- by addarith [hq₁, hk]
  calc b * q < a := hq₁
    _ = b * k := hk
  cancel b at h2
  have : q + 1 ≤ k := by addarith [h2]
  have : ¬k < q + 1 := not_lt_of_ge this
  contradiction

example {p : ℕ} (hp : 2 ≤ p)  (T : ℕ) (hTp : p < T ^ 2)
    (H : ∀ (m : ℕ), 1 < m → m < T → ¬ (m ∣ p)) :
    Prime p := by
  apply prime_test hp
  intro m hm1 hmp
  obtain hmT | hmT := lt_or_le m T
  · apply H m hm1 hmT
  intro h_div
  obtain ⟨l, hl⟩ := h_div
  have : l ∣ p
  · use m
    rw [hl]
    ring
  have hl1 :=
    calc m * 1 = m := by ring
      _ < p := hmp
      _ = m * l := hl
  cancel m at hl1
  have hl2 : l < T
  · have : T * l < T * T :=
    calc T * l ≤ m * l := by rel [hmT]
      _ = p := by rw [hl]
      _ < T ^ 2 := by rel [hTp]
      _ = T * T := by ring
    cancel T at this
  have : ¬ l ∣ p := H l hl1 hl2
  contradiction


example : Prime 79 := by
  apply better_prime_test (T := 9)
  · numbers
  · numbers
  intro m hm1 hm2
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 39
    constructor <;> numbers
  · use 26
    constructor <;> numbers
  · use 19
    constructor <;> numbers
  · use 15
    constructor <;> numbers
  · use 13
    constructor <;> numbers
  · use 11
    constructor <;> numbers
  · use 9
    constructor <;> numbers

/-! # Exercises -/


example : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  intro h1
  obtain ⟨x, h2, h3⟩ := h1
  have h4 : 5 ≤ 4 := by addarith [h2, h3]
  numbers at h4

example : ¬ (∃ a : ℝ, a ^ 2 ≤ 8 ∧ a ^ 3 ≥ 30) := by
  intro h1
  obtain ⟨x, h2, h3⟩ := h1
  have h4 : x ^ 6 ≤ 512 :=
  calc x ^ 6 = x ^ 2 * x ^ 2 * x ^ 2 := by ring
    _ ≤ 8 * 8 * 8 := by rel [h2]
    _ = 512 := by numbers
  have h5 : x ^ 6 ≥ 900 :=
  calc x ^ 6 = x ^ 3 * x ^ 3 := by ring
    _ ≥ 30 * 30 := by rel [h3]
    _ = 900 := by numbers
  have h6 : 900 ≤ 512 := by addarith [h4, h5]
  numbers at h6

example : ¬ Int.Even 7 := by
  intro h1
  rw [Int.even_iff_modEq] at h1
  have h2 : 1 ≡ 0 [ZMOD 2] :=
  calc 1 ≡ 1 + 2 * 3 [ZMOD 2] := by extra
    _ = 7 := by ring
    _ ≡ 0 [ZMOD 2] := by rel [h1]
  numbers at h2

example {n : ℤ} (hn : n + 3 = 7) : ¬ (Int.Even n ∧ n ^ 2 = 10) := by
  intro h1
  obtain ⟨h2, h3⟩ := h1
  have h4 : n = 4 := by addarith [hn]
  rw [h4] at h3
  numbers at h3

example {x : ℝ} (hx : x ^ 2 < 9) : ¬ (x ≤ -3 ∨ x ≥ 3) := by
  intro h1
  obtain h2 | h3 := h1
  · have h4 : -x ≥ 3 := by addarith [h2]
    have h5 : x ^ 2 ≥ 9 :=
    calc x ^ 2 = -x * -x := by ring
      _ ≥ 3 * 3 := by rel [h4]
      _ = 9 := by numbers
    have h6 : ¬x ^ 2 < 9 := not_lt_of_ge h5
    contradiction
  · have h7 : x ^ 2 ≥ 9 :=
    calc x ^ 2 = x * x := by ring
      _ ≥ 3 * 3 := by rel [h3]
      _ = 9 := by numbers
    have h8 : ¬x ^ 2 < 9 := not_lt_of_ge h7
    contradiction

example : ¬ (∃ N : ℕ, ∀ k > N, Nat.Even k) := by
  intro h1
  obtain ⟨a, h2⟩ := h1
  obtain h3 | h4 := Nat.even_or_odd a
  · obtain ⟨b, h5⟩ := h3
    have h6 : 2 * b + 1 > a := by addarith [h5]
    have h7 : Nat.Even (2 * b + 1) := h2 (2 * b + 1) h6
    have h8 : Nat.Odd (2 * b + 1)
    · use b
      ring
    rw [Nat.even_iff_not_odd] at h7
    contradiction
  · obtain ⟨c, h9⟩ := h4
    have h10 : 2 * c + 3 > a := by addarith [h9]
    have h11 : Nat.Even (2 * c + 3) := h2 (2 * c + 3) h10
    have h12 : Nat.Odd (2 * c + 3)
    · use c + 1
      ring
    rw [Nat.even_iff_not_odd] at h11
    contradiction

example (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 4]) := by
  sorry

example : ¬ Prime 1 := by
  sorry

example : Prime 97 := by
  sorry
