/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Basic
import Library.Theory.ModEq.Defs

math2001_init


example : 11 ≡ 3 [ZMOD 4] := by
  use 2
  numbers

example : -5 ≡ 1 [ZMOD 3] := by
  -- dsimp [Int.ModEq, Dvd.dvd]
  use -2
  numbers

theorem Int.ModEq.add {n a b c d : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
    a + c ≡ b + d [ZMOD n] := by
  dsimp [Int.ModEq] at *
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use x + y
  calc
    a + c - (b + d) = a - b + (c - d) := by ring
    _ = n * x + n * y := by rw [hx, hy]
    _ = n * (x + y) := by ring


theorem Int.ModEq.sub {n a b c d : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
    a - c ≡ b - d [ZMOD n] := by
  obtain ⟨x, h3⟩ := h1
  obtain ⟨y, h4⟩ := h2
  use x - y
  have h5 :  a - c - (b - d) = a - b - (c - d) := by ring
  rw [h5, h3, h4]
  ring

theorem Int.ModEq.neg {n a b : ℤ} (h1 : a ≡ b [ZMOD n]) : -a ≡ -b [ZMOD n] := by
  obtain ⟨x, h2⟩ := h1
  use -x
  have h3 : -a - -b = -(a - b) := by ring
  rw [h3, h2]
  ring

theorem Int.ModEq.mul {n a b c d : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
    a * c ≡ b * d [ZMOD n] := by
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use x * c + b * y
  calc
    a * c - b * d = (a - b) * c + b * (c - d) := by ring
    _ = n * x * c + b * (n * y) := by rw [hx, hy]
    _ = n * (x * c + b * y) := by ring


theorem Int.ModEq.pow_two (h : a ≡ b [ZMOD n]) : a ^ 2 ≡ b ^ 2 [ZMOD n] := by
  obtain ⟨x, hx⟩ := h
  use x * (a + b)
  calc
    a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
    _ = n * x * (a + b) := by rw [hx]
    _ = n * (x * (a + b)) := by ring


theorem Int.ModEq.pow_three (h : a ≡ b [ZMOD n]) : a ^ 3 ≡ b ^ 3 [ZMOD n] := by
  apply Int.ModEq.mul
  · apply Int.ModEq.pow_two
    apply h
  · apply h

theorem Int.ModEq.pow (k : ℕ) (h : a ≡ b [ZMOD n]) : a ^ k ≡ b ^ k [ZMOD n] :=
  sorry -- we'll prove this later in the book


theorem Int.ModEq.refl (a : ℤ) : a ≡ a [ZMOD n] := by
  use 0
  ring


example {a b : ℤ} (ha : a ≡ 2 [ZMOD 4]) :
    a * b ^ 2 + a ^ 2 * b + 3 * a ≡ 2 * b ^ 2 + 2 ^ 2 * b + 3 * 2 [ZMOD 4] := by
  obtain ⟨x, hx⟩ := ha
  use x * (b ^ 2 + a * b + 2 * b + 3)
  calc
    a * b ^ 2 + a ^ 2 * b + 3 * a - (2 * b ^ 2 + 2 ^ 2 * b + 3 * 2) =
        (a - 2) * (b ^ 2 + a * b + 2 * b + 3) :=
      by ring
    _ = 4 * x * (b ^ 2 + a * b + 2 * b + 3) := by rw [hx]
    _ = 4 * (x * (b ^ 2 + a * b + 2 * b + 3)) := by ring


example {a b : ℤ} (ha : a ≡ 2 [ZMOD 4]) :
    a * b ^ 2 + a ^ 2 * b + 3 * a ≡ 2 * b ^ 2 + 2 ^ 2 * b + 3 * 2 [ZMOD 4] := by
  apply Int.ModEq.add
  apply Int.ModEq.add
  apply Int.ModEq.mul
  apply ha
  apply Int.ModEq.refl
  apply Int.ModEq.mul
  apply Int.ModEq.pow
  apply ha
  apply Int.ModEq.refl
  apply Int.ModEq.mul
  apply Int.ModEq.refl
  apply ha

/-! # Exercises -/


example : 34 ≡ 104 [ZMOD 5] := by
  use -14
  numbers

theorem Int.ModEq.symm (h : a ≡ b [ZMOD n]) : b ≡ a [ZMOD n] := by
  obtain ⟨x, h1⟩ := h
  use -x
  have h2 : b - a = -(a - b) := by ring
  rw [h2, h1]
  ring

theorem Int.ModEq.trans (h1 : a ≡ b [ZMOD n]) (h2 : b ≡ c [ZMOD n]) :
    a ≡ c [ZMOD n] := by
  obtain ⟨x, h3⟩ := h1
  obtain ⟨y, h4⟩ := h2
  use x + y
  have h5 : a - c = (a - b) + (b - c) := by ring
  rw [h5, h3, h4]
  ring

example : a + n * c ≡ a [ZMOD n] := by
  use c
  ring

/-
theorem Int.ModEq.div : ∃ n a b c d : ℤ,
    a ≡ b [ZMOD n] ∧ c ≡ d [ZMOD n] ∧ ¬ Int.div a c ≡ Int.div b d [ZMOD n] := by
  use 2, 20, 4, 4, 2
  have h : Int.div 20 4 - Int.div 4 2 = 3 := by rfl
  constructor
  · use 8
    numbers
  · constructor
    · use 1
      numbers
    · apply Int.not_dvd_of_exists_lt_and_lt
      use 1
      rw [h]
      constructor
      · numbers
      · numbers
-/

example {a b : ℤ} (h : a ≡ b [ZMOD 5]) : 2 * a + 3 ≡ 2 * b + 3 [ZMOD 5] := by
  obtain ⟨x, h1⟩ := h
  use 2 * x
  have h2 : 2 * a + 3 - (2 * b + 3) = 2 * (a - b) := by ring
  rw [h2, h1]
  ring

example {a b : ℤ} (h : a ≡ b [ZMOD 5]) : 2 * a + 3 ≡ 2 * b + 3 [ZMOD 5] := by
  apply Int.ModEq.add
  · apply Int.ModEq.mul
    · apply Int.ModEq.refl
    · apply h
  · apply Int.ModEq.refl

example {m n : ℤ} (h : m ≡ n [ZMOD 4]) : 3 * m - 1 ≡ 3 * n - 1 [ZMOD 4] := by
  obtain ⟨x, h1⟩ := h
  use 3 * x
  have h2 : 3 * m - 1 - (3 * n - 1) = 3 * (m - n) := by ring
  rw [h2, h1]
  ring

example {m n : ℤ} (h : m ≡ n [ZMOD 4]) : 3 * m - 1 ≡ 3 * n - 1 [ZMOD 4] := by
  apply Int.ModEq.add
  · apply Int.ModEq.mul
    · apply Int.ModEq.refl
    · apply h
  · apply Int.ModEq.refl

example {k : ℤ} (hb : k ≡ 3 [ZMOD 5]) :
    4 * k + k ^ 3 + 3 ≡ 4 * 3 + 3 ^ 3 + 3 [ZMOD 5] := by
  obtain ⟨x, h1⟩ := hb
  use x * (k * (k + 3) + 13)
  have h2 : 4 * k + k ^ 3 + 3 - (4 * 3 + 3 ^ 3 + 3) = (k - 3) * (k * (k + 3) + 13) := by ring
  rw [h2, h1]
  ring

example {k : ℤ} (hb : k ≡ 3 [ZMOD 5]) :
    4 * k + k ^ 3 + 3 ≡ 4 * 3 + 3 ^ 3 + 3 [ZMOD 5] := by
  apply Int.ModEq.add
  · apply Int.ModEq.add
    · apply Int.ModEq.mul
      · apply Int.ModEq.refl
      · apply hb
    · apply Int.ModEq.pow
      apply hb
  · apply Int.ModEq.refl
