/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Basic

math2001_init

open Int


example : Odd (7 : ℤ) := by
  dsimp [Odd]
  use 3
  numbers


example : Odd (-3 : ℤ) := by
  dsimp [Odd]
  use -2
  numbers

example {n : ℤ} (hn : Odd n) : Odd (3 * n + 2) := by
  dsimp [Odd] at *
  obtain ⟨k, hk⟩ := hn
  use 3 * k + 2
  calc
    3 * n + 2 = 3 * (2 * k + 1) + 2 := by rw [hk]
    _ = 2 * (3 * k + 2) + 1 := by ring


example {n : ℤ} (hn : Odd n) : Odd (7 * n - 4) := by
  dsimp [Odd] at *
  obtain ⟨k, hk⟩ := hn
  use 7 * k + 1
  rw [hk]
  ring

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x + y + 1) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use a + b + 1
  calc
    x + y + 1 = 2 * a + 1 + (2 * b + 1) + 1 := by rw [ha, hb]
    _ = 2 * (a + b + 1) + 1 := by ring


example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y + 2 * y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use 2 * a * b + 3 * b + a + 1
  calc x * y + 2 * y = (2 * a + 1) * (2 * b + 1) + 2 * (2 * b + 1) := by rw [ha, hb]
    _ = 2 * (2 * a * b + 3 * b + a + 1) + 1 := by ring

example {m : ℤ} (hm : Odd m) : Even (3 * m - 5) := by
  obtain ⟨t, ht⟩ := hm
  use 3 * t - 1
  calc 3 * m - 5 = 3 * (2 * t + 1) - 5 := by rw [ht]
    _ = 2 * (3 * t - 1) := by ring

example {n : ℤ} (hn : Even n) : Odd (n ^ 2 + 2 * n - 5) := by
  obtain ⟨k, hk⟩ := hn
  use 2 * k ^ 2 + 2 * k - 3
  rw [hk]
  ring

example (n : ℤ) : Even (n ^ 2 + n + 4) := by
  obtain hn | hn := Int.even_or_odd n
  · obtain ⟨x, hx⟩ := hn
    use 2 * x ^ 2 + x + 2
    calc
      n ^ 2 + n + 4 = (2 * x) ^ 2 + 2 * x + 4 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + x + 2) := by ring
  · obtain ⟨x, hx⟩ := hn
    use 2 * x ^ 2 + 3 * x + 3
    calc
      n ^ 2 + n + 4 = (2 * x + 1) ^ 2 + (2 * x + 1) + 4 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + 3 * x + 3) := by ring

/-! # Exercises -/


example : Odd (-9 : ℤ) := by
  use -5
  numbers

example : Even (26 : ℤ) := by
  use 13
  numbers

example {m n : ℤ} (hm : Odd m) (hn : Even n) : Odd (n + m) := by
  obtain ⟨x, hx⟩ := hn
  obtain ⟨y, hy⟩ := hm
  use x + y
  rw [hx, hy]
  ring

example {p q : ℤ} (hp : Odd p) (hq : Even q) : Odd (p - q - 4) := by
  obtain ⟨x, hx⟩ := hp
  obtain ⟨y, hy⟩ := hq
  use x - y - 2
  rw [hx, hy]
  ring

example {a b : ℤ} (ha : Even a) (hb : Odd b) : Even (3 * a + b - 3) := by
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  use 3 * x + y - 1
  rw [hx, hy]
  ring

example {r s : ℤ} (hr : Odd r) (hs : Odd s) : Even (3 * r - 5 * s) := by
  obtain ⟨x, hx⟩ := hr
  obtain ⟨y, hy⟩ := hs
  use 3 * x - 5 * y - 1
  rw [hx, hy]
  ring

example {x : ℤ} (hx : Odd x) : Odd (x ^ 3) := by
  obtain ⟨k, hk⟩ := hx
  use k * (3 + k * (4 * k + 6))
  rw [hk]
  ring

example {n : ℤ} (hn : Odd n) : Even (n ^ 2 - 3 * n + 2) := by
  obtain ⟨k, hk⟩ := hn
  use k * (2 * k - 1)
  rw [hk]
  ring

example {a : ℤ} (ha : Odd a) : Odd (a ^ 2 + 2 * a - 4) := by
  obtain ⟨k, hk⟩ := ha
  use k * (2 * k + 4) - 1
  rw [hk]
  ring

example {p : ℤ} (hp : Odd p) : Odd (p ^ 2 + 3 * p - 5) := by
  obtain ⟨k, hk⟩ := hp
  use k * (2 * k + 5) - 1
  rw [hk]
  ring

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use 2 * a * b + a + b
  rw [ha, hb]
  ring

example (n : ℤ) : Odd (3 * n ^ 2 + 3 * n - 1) := by
  obtain hn1 | hn2 : Even n ∨ Odd n := Int.even_or_odd n
  · obtain ⟨x, hx⟩ := hn1
    use x * (6 * x + 3) - 1
    rw [hx]
    ring
  · obtain ⟨y, hy⟩ := hn2
    use y * (6 * y + 9) + 2
    rw [hy]
    ring

example (n : ℤ) : ∃ m ≥ n, Odd m := by
  obtain hn1 | hn2 : Even n ∨ Odd n := Int.even_or_odd n
  · obtain ⟨x, hx⟩ := hn1
    use 2 * x + 1
    constructor
    · addarith [hx]
    · use x
      ring
  · obtain ⟨y, hy⟩ := hn2
    use 2 * y + 3
    constructor
    · addarith [hy]
    · use y + 1
      ring

example (a b c : ℤ) : Even (a - b) ∨ Even (a + c) ∨ Even (b - c) := by
  obtain ha1 | ha2 : Even a ∨ Odd a := Int.even_or_odd a
  · obtain ⟨x, hx⟩ := ha1
    obtain hb1 | hb2 : Even b ∨ Odd b := Int.even_or_odd b
    · obtain ⟨y, hy⟩ := hb1
      left
      use x - y
      rw [hx, hy]
      ring
    · obtain ⟨y, hy⟩ := hb2
      right
      obtain hc1 | hc2 : Even c ∨ Odd c := Int.even_or_odd c
      · obtain ⟨z, hz⟩ := hc1
        left
        use x + z
        rw [hx, hz]
        ring
      · obtain ⟨z, hz⟩ := hc2
        right
        use y - z
        rw [hy, hz]
        ring
  · obtain ⟨x, hx⟩ := ha2
    obtain hb1 | hb2 : Even b ∨ Odd b := Int.even_or_odd b
    · obtain ⟨y, hy⟩ := hb1
      right
      obtain hc1 | hc2 : Even c ∨ Odd c := Int.even_or_odd c
      · obtain ⟨z, hz⟩ := hc1
        right
        use y - z
        rw [hy, hz]
        ring
      · obtain ⟨z, hz⟩ := hc2
        left
        use x + z + 1
        rw [hx, hz]
        ring
    · obtain ⟨y, hy⟩ := hb2
      left
      use x - y
      rw [hx, hy]
      ring
