import Erdos1201.Smooth.PrimeBand

/-!
# Counting nonsmooth integers using large prime divisors

The original Erdős #1201 deduction is by Przemek Chojecki together with
ChatGPT 5.5. All estimates in this module are finite counting statements.
All declarations have been compiler-checked.
-/

open Finset
open scoped BigOperators

namespace Erdos1201.SmoothRoute
open Classical

noncomputable def primeMultiples (X p : ℕ) : Finset ℕ :=
  (Ioc X (2 * X)).filter (fun n => p ∣ n)

/-- Exact count of multiples in the half-open counting interval. -/
theorem card_primeMultiples {X p : ℕ} (hp : 0 < p) :
    (primeMultiples X p).card = (2 * X) / p - X / p := by
  have heq : primeMultiples X p =
      (Ioc (X / p) ((2 * X) / p)).image (fun q => q * p) := by
    ext n
    simp only [primeMultiples, mem_filter, mem_Ioc, mem_image]
    constructor
    · rintro ⟨⟨hlo, hhi⟩, hdiv⟩
      have hd : n / p * p = n := Nat.div_mul_cancel hdiv
      refine ⟨n / p, ⟨?_, ?_⟩, hd⟩
      · exact (Nat.div_lt_iff_lt_mul hp).mpr (by simpa [hd] using hlo)
      · exact (Nat.le_div_iff_mul_le hp).mpr (by simpa [hd] using hhi)
    · rintro ⟨q, ⟨hlo, hhi⟩, rfl⟩
      exact ⟨⟨(Nat.div_lt_iff_lt_mul hp).mp hlo,
        (Nat.le_div_iff_mul_le hp).mp hhi⟩, dvd_mul_left p q⟩
  rw [heq, card_image_of_injective]
  · simp
  · intro a b hab
    exact Nat.eq_of_mul_eq_mul_right hp hab

/-- Rounding loses at most one from the expected number of multiples. -/
theorem card_primeMultiples_lower {X p : ℕ} (hp : 0 < p) :
    (X : ℝ) / p - 1 ≤ ((primeMultiples X p).card : ℝ) := by
  rw [card_primeMultiples hp,
    Nat.cast_sub (Nat.div_le_div_right (show X ≤ 2 * X by omega))]
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hu : (↑(X / p) : ℝ) * p ≤ X := by
    exact_mod_cast Nat.div_mul_le_self X p
  have he := congrArg (fun n : ℕ => (n : ℝ)) (Nat.div_add_mod (2 * X) p)
  push_cast at he
  have hm : (↑((2 * X) % p) : ℝ) < p := by
    exact_mod_cast Nat.mod_lt (2 * X) hp
  have hd : (X : ℝ) / p ≤ ↑((2 * X) / p) - ↑(X / p) + 1 := by
    apply (div_le_iff₀ hpR).mpr
    nlinarith
  linarith

/-- Two distinct prime divisors above the square-root scale cannot occur. -/
theorem card_large_prime_divisors_le_one {X : ℕ} {Y : ℝ} {S : Finset ℕ}
    (hY : 0 ≤ Y) (hsize : 2 * (X : ℝ) < Y ^ 2)
    (hprime : ∀ p ∈ S, p.Prime) (hcut : ∀ p ∈ S, Y < (p : ℝ))
    {n : ℕ} (hn : n ∈ Ioc X (2 * X)) :
    (S.filter (fun p => p ∣ n)).card ≤ 1 := by
  apply card_le_one.mpr
  intro p hp q hq
  have hpS := (mem_filter.mp hp).1
  have hqS := (mem_filter.mp hq).1
  by_contra hne
  have hcop : Nat.Coprime p q := (Nat.coprime_primes (hprime p hpS) (hprime q hqS)).mpr hne
  have hd : p * q ∣ n := hcop.mul_dvd_of_dvd_of_dvd
    (mem_filter.mp hp).2 (mem_filter.mp hq).2
  have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le X) (mem_Ioc.mp hn).1
  have hpn : p * q ≤ n := Nat.le_of_dvd hnpos hd
  have hpnR : (p : ℝ) * q ≤ 2 * X := by
    exact_mod_cast hpn.trans (mem_Ioc.mp hn).2
  have hpY := hcut p hpS
  have hqY := hcut q hqS
  have hprod : Y ^ 2 < (p : ℝ) * q := by
    nlinarith [mul_pos (sub_pos.mpr hpY) (sub_pos.mpr hqY)]
  linarith

/-- The incidence count of large prime divisors is bounded by nonsmooth mass. -/
theorem sum_primeMultiples_le_nonsmooth {X : ℕ} {Y : ℝ} {S : Finset ℕ}
    (hY : 0 ≤ Y) (hsize : 2 * (X : ℝ) < Y ^ 2)
    (hprime : ∀ p ∈ S, p.Prime) (hcut : ∀ p ∈ S, Y < (p : ℝ)) :
    (∑ p ∈ S, ((primeMultiples X p).card : ℝ)) ≤
      (X : ℝ) - ∑ n ∈ Ioc X (2 * X), smoothIndicator Y n := by
  have hpoint : ∀ n ∈ Ioc X (2 * X),
      ((S.filter (fun p => p ∣ n)).card : ℝ) ≤ 1 - smoothIndicator Y n := by
    intro n hn
    by_cases hs : Smooth Y n
    · have he : S.filter (fun p => p ∣ n) = ∅ := by
        apply filter_eq_empty_iff.mpr
        intro p hp hd
        exact (not_lt_of_ge (hs.2 p (hprime p hp) hd)) (hcut p hp)
      simp [he, smoothIndicator, hs]
    · have hc : ((S.filter (fun p => p ∣ n)).card : ℝ) ≤ 1 := by
        exact_mod_cast card_large_prime_divisors_le_one hY hsize hprime hcut hn
      simpa [smoothIndicator, hs] using hc
  calc
    _ = ∑ p ∈ S, ∑ n ∈ Ioc X (2 * X), if p ∣ n then (1 : ℝ) else 0 := by
      apply sum_congr rfl
      intro p hp
      simp [primeMultiples]
    _ = ∑ n ∈ Ioc X (2 * X), ∑ p ∈ S, if p ∣ n then (1 : ℝ) else 0 := sum_comm
    _ = ∑ n ∈ Ioc X (2 * X), ((S.filter (fun p => p ∣ n)).card : ℝ) := by
      simp
    _ ≤ ∑ n ∈ Ioc X (2 * X), (1 - smoothIndicator Y n) := sum_le_sum hpoint
    _ = _ := by
      rw [sum_sub_distrib]
      simp [show 2 * X - X = X by omega]

/-- Exact conversion from inclusive smooth counts to an interval sum. -/
theorem smoothCount_sub_eq_sum (Y : ℝ) (X : ℕ) :
    smoothCount Y (2 * X) - smoothCount Y X =
      ∑ n ∈ Ioc X (2 * X), smoothIndicator Y n := by
  have h := sum_range_add_sum_Ico (smoothIndicator Y)
    (show X + 1 ≤ 2 * X + 1 by omega)
  rw [Ico_add_one_add_one_eq_Ioc] at h
  unfold smoothCount
  linarith

/-- A finite upper bound for the smooth mean from the reciprocal mass of a prime band. -/
theorem blockMean_le_of_primeBand {X : ℕ} {Y B : ℝ}
    (hX : 0 < X) (hY : 0 ≤ Y) (hB : 0 ≤ B)
    (hsize : 2 * (X : ℝ) < Y ^ 2) :
    blockMean (smoothIndicator Y) X ≤
      1 - primeReciprocal Y B + (B + 1) / (X : ℝ) := by
  let S := primeBand Y B
  have hprime : ∀ p ∈ S, p.Prime := fun p hp => (mem_filter.mp hp).2
  have hcut : ∀ p ∈ S, Y < (p : ℝ) := by
    intro p hp
    exact (Nat.floor_lt hY).mp (mem_Ioc.mp (mem_filter.mp hp).1).1
  have hsum := sum_primeMultiples_le_nonsmooth hY hsize hprime hcut
  have hfloor : (X : ℝ) * primeReciprocal Y B - S.card ≤
      ∑ p ∈ S, ((primeMultiples X p).card : ℝ) := by
    calc
      _ = ∑ p ∈ S, ((X : ℝ) / p - 1) := by
        simp [S, primeReciprocal, sum_sub_distrib, mul_sum, div_eq_mul_inv]
      _ ≤ _ := sum_le_sum (fun p hp => card_primeMultiples_lower (hprime p hp).pos)
  have hcard : (S.card : ℝ) ≤ B := by
    have hsub : S ⊆ Ioc 0 ⌊B⌋₊ := by
      intro p hp
      exact mem_Ioc.mpr ⟨(hprime p hp).pos, (mem_Ioc.mp (mem_filter.mp hp).1).2⟩
    have hn : S.card ≤ ⌊B⌋₊ := by simpa using card_le_card hsub
    exact (Nat.cast_le.mpr hn).trans (Nat.floor_le hB)
  have he := smoothIndicator_sub_le_one Y X (2 * X)
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  rw [blockMean_smoothIndicator_eq, smoothCount_sub_eq_sum]
  apply (div_le_iff₀ hXR).mpr
  have hr : (1 - primeReciprocal Y B + (B + 1) / (X : ℝ)) * X =
      (X : ℝ) - X * primeReciprocal Y B + B + 1 := by
    field_simp
    ring
  rw [hr]
  linarith

end Erdos1201.SmoothRoute
