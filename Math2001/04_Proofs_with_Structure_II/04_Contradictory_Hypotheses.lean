/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init


example {y : ℝ} (x : ℝ) (h : 0 < x * y) (hx : 0 ≤ x) : 0 < y := by
  obtain hneg | hpos : y ≤ 0 ∨ 0 < y := le_or_lt y 0
  · -- the case `y ≤ 0`
    have : ¬0 < x * y
    · apply not_lt_of_ge
      calc
        0 = x * 0 := by ring
        _ ≥ x * y := by rel [hneg]
    contradiction
  · -- the case `0 < y`
    apply hpos


example {t : ℤ} (h2 : t < 3) (h : t - 1 = 6) : t = 13 := by
  have H :=
  calc
    7 = t := by addarith [h]
    _ < 3 := h2
  have : ¬(7 : ℤ) < 3 := by numbers
  contradiction


example {t : ℤ} (h2 : t < 3) (h : t - 1 = 6) : t = 13 := by
  have H :=
  calc
    7 = t := by addarith [h]
    _ < 3 := h2
  numbers at H -- this is a contradiction!


example (n : ℤ) (hn : n ^ 2 + n + 1 ≡ 1 [ZMOD 3]) :
    n ≡ 0 [ZMOD 3] ∨ n ≡ 2 [ZMOD 3] := by
  mod_cases h : n % 3
  · -- case 1: `n ≡ 0 [ZMOD 3]`
    left
    apply h
  · -- case 2: `n ≡ 1 [ZMOD 3]`
    have H :=
      calc 0 ≡ 0 + 3 * 1 [ZMOD 3] := by extra
      _ = 1 ^ 2 + 1 + 1 := by numbers
      _ ≡ n ^ 2 + n + 1 [ZMOD 3] := by rel [h]
      _ ≡ 1 [ZMOD 3] := hn
    numbers at H -- contradiction!
  · -- case 3: `n ≡ 2 [ZMOD 3]`
    right
    apply h


example {p : ℕ} (hp : 2 ≤ p) (H : ∀ m : ℕ, 1 < m → m < p → ¬m ∣ p) : Prime p := by
  constructor
  · apply hp -- show that `2 ≤ p`
  intro m hmp
  have hp' : 0 < p := by extra
  have h1m : 1 ≤ m := Nat.pos_of_dvd_of_pos hmp hp'
  obtain hm | hm_left : 1 = m ∨ 1 < m := eq_or_lt_of_le h1m
  · -- the case `m = 1`
    left
    addarith [hm]
  -- the case `1 < m`
  · have h1mp : m ≤ p := Nat.le_of_dvd hp' hmp
    obtain h2mp | h2mp_right : m = p ∨ m < p := eq_or_lt_of_le h1mp
    · right
      apply h2mp
    · have : ¬m ∣ p -- := H m hm_left h2mp_left
      · apply H
        · apply hm_left
        · apply h2mp_right
      contradiction

example : Prime 5 := by
  apply prime_test
  · numbers
  intro m hm_left hm_right
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 2
    constructor <;> numbers
  · use 1
    constructor <;> numbers
  · use 1
    constructor <;> numbers


example {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h_pyth : a ^ 2 + b ^ 2 = c ^ 2) : 3 ≤ a := by
  obtain h1 | h2 : a ≤ 2 ∨ 3 ≤ a := le_or_succ_le a 2
  · obtain h3 | h4 : b ≤ 1 ∨ 2 ≤ b := le_or_succ_le b 1
    · have h5 : c ^ 2 < 3 ^ 2 :=
      calc c ^ 2 = a ^ 2 + b ^ 2 := by rw [h_pyth]
        _ ≤ 2 ^ 2 + 1 ^ 2 := by rel [h1, h3]
        _ < 3 ^ 2 := by numbers
      cancel 2 at h5
      interval_cases c <;> interval_cases a <;> interval_cases b <;> numbers at h_pyth
    · have h6 : b ^ 2 < c ^ 2 :=
      calc b ^ 2 < a ^ 2 + b ^ 2 := by extra
        _ = c ^ 2 := h_pyth
      cancel 2 at h6
      have h7 : b + 1 ≤ c := by addarith [h6]
      have h8 : c ^ 2 < (b + 1) ^ 2 :=
      calc c ^ 2 = a ^ 2 + b ^ 2 := by rw [h_pyth]
        _ ≤ 2 ^ 2 + b ^ 2 := by rel [h1]
        _ = b ^ 2 + 2 * 2 := by ring
        _ ≤ b ^ 2 + 2 * b := by rel [h4]
        _ < b ^ 2 + 2 * b + 1 := by extra
        _ = (b + 1) ^ 2 := by ring
      cancel 2 at h8
      have h9 : ¬b + 1 ≤ c := not_le_of_gt h8 -- ¬c < b + 1 := not_lt_of_ge h7
      contradiction
  · apply h2

/-! # Exercises -/


example {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hn : 0 < n) (h : y ^ n ≤ x ^ n) :
    y ≤ x := by
  obtain h1 | h2 : y ≤ x ∨ x < y := le_or_lt y x
  · apply h1
  · have h3 : y ^ n > x ^ n := by rel [h2]
    have h4 : ¬y ^ n ≤ x ^ n := not_le_of_gt h3
    contradiction

example (n : ℤ) (hn : n ^ 2 ≡ 4 [ZMOD 5]) : n ≡ 2 [ZMOD 5] ∨ n ≡ 3 [ZMOD 5] := by
  mod_cases h : n % 5
  · have : 0 ^ 2 ≡ 4 [ZMOD 5] :=
    calc 0 ^ 2 ≡ n ^ 2 [ZMOD 5] := by rel [h]
      _ ≡ 4 [ZMOD 5] := hn
    numbers at this
  · have : 1 ^ 2 ≡ 4 [ZMOD 5] :=
    calc 1 ^ 2 ≡ n ^ 2 [ZMOD 5] := by rel [h]
      _ ≡ 4 [ZMOD 5] := hn
    numbers at this
  · left
    apply h
  · right
    apply h
  · have : 1 ≡ 4 [ZMOD 5] :=
    calc 1 ≡ 1 + 5 * 3 [ZMOD 5] := by extra
      _ = 4 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 5] := by rel [h]
      _ ≡ 4 [ZMOD 5] := hn
    numbers at this

example : Prime 7 := by
  apply prime_test
  · numbers
  · intro m h1 h2
    apply Nat.not_dvd_of_exists_lt_and_lt
    interval_cases m
    · use 3
      constructor <;> numbers
    · use 2
      constructor <;> numbers
    · use 1
      constructor <;> numbers
    · use 1
      constructor <;> numbers
    · use 1
      constructor <;> numbers

example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
  have h3 :=
    calc
      (x + 2) * (x - 2) = x ^ 2 + 2 * x - 2 * x - 4 := by ring
      _ = 0 := by addarith [h1]
  rw [mul_eq_zero] at h3
  obtain h4 | h5 := h3
  · have h6 : 3 < 0 := by addarith [h2, h4]
    numbers at h6
  · addarith [h5]

namespace Nat

example (p : ℕ) (h : Prime p) : p = 2 ∨ Odd p := by
  obtain h1 | h2 : p ≤ 2 ∨ 3 ≤ p := le_or_succ_le p 2 <;> obtain ⟨h3, h4⟩ := h
  · left
    apply le_antisymm h1 h3
  · right
    obtain h6 | h7 : Even p ∨ Odd p := even_or_odd p <;> obtain ⟨k, h8⟩ := h6
    · have h9 : 2 ∣ p <;> use k
      · apply h8
      obtain h10 | h11 : 2 = 1 ∨ 2 = p := h4 2 h9 -- ; apply h4 ; apply h9
      · numbers at h10
      · have h12 : 3 ≤ 2 := by addarith [h2, h11]
        numbers at h12
    · apply h7
