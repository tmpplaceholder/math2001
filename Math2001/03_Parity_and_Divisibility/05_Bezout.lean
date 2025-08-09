/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Basic

math2001_init


example {n : ℤ} (hn : 8 ∣ 5 * n) : 8 ∣ n := by
  obtain ⟨a, ha⟩ := hn
  use -3 * a + 2 * n
  calc
    n = -3 * (5 * n) + 16 * n := by ring
    _ = -3 * (8 * a) + 16 * n := by rw [ha]
    _ = 8 * (-3 * a + 2 * n) := by ring


example {n : ℤ} (hn : 8 ∣ 5 * n) : 8 ∣ n := by
  obtain ⟨a, ha⟩ := hn
  use 5 * a - 3 * n
  calc
    n = 5 * (5 * n) - 24 * n := by ring
    _ = 5 * (8 * a) - 24 * n := by rw [ha]
    _ = 8 * (5 * a - 3 * n) := by ring

example {n : ℤ} (h1 : 5 ∣ 3 * n) : 5 ∣ n := by
  obtain ⟨x, hx⟩ := h1
  use 2 * x - n
  calc
    n = 2 * (3 * n) - 5 * n := by ring
    _ = 2 * (5 * x) - 5 * n := by rw [hx]
    _ = 5 * (2 * x - n) := by ring

example {m : ℤ} (h1 : 8 ∣ m) (h2 : 5 ∣ m) : 40 ∣ m := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  use -3 * a + 2 * b
  calc
    m = -15 * m + 16 * m := by ring
    _ = -15 * (8 * a) + 16 * m := by rw [ha]
    _ = -15 * (8 * a) + 16 * (5 * b) := by rw [hb]
    _ = 40 * (-3 * a + 2 * b) := by ring

/-! # Exercises -/


example {n : ℤ} (hn : 6 ∣ 11 * n) : 6 ∣ n := by
  obtain ⟨c, h1⟩ := hn
  have h2 : n = 5 * (11 * n) - 54 * n := by ring
  rw [h2, h1]
  use 5 * c - 9 * n
  ring

example {a : ℤ} (ha : 7 ∣ 5 * a) : 7 ∣ a := by
  obtain ⟨c, h1⟩ := ha
  have h2 : a = 3 * (5 * a) - 14 * a := by ring
  rw [h2, h1]
  use 3 * c - 2 * a
  ring

example {n : ℤ} (h1 : 7 ∣ n) (h2 : 9 ∣ n) : 63 ∣ n := by
  obtain ⟨a, h3⟩ := h1
  obtain ⟨b, h4⟩ := h2
  have h5 : n = 28 * n - 27 * n := by ring
  have h6 : 28 * n - 27 * n = 28 * n - 27 * (7 * a) := by rw [h3]
  rw [h5, h6, h4]
  use 4 * b - 3 * a
  ring

example {n : ℤ} (h1 : 5 ∣ n) (h2 : 13 ∣ n) : 65 ∣ n := by
  obtain ⟨a, h3⟩ := h1
  obtain ⟨b, h4⟩ := h2
  have h5 : n = 26 * n - 25 * n := by ring
  have h6 : 26 * n - 25 * n = 26 * (5 * a) - 25 * n := by rw [h3]
  rw [h5, h6, h4]
  use 2 * a - 5 * b
  ring
