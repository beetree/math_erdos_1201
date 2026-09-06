module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Erase
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.GCD.BigOperators
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.SetLike.Basic
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Disjoint
public import Mathlib.Order.Interval.Finset.Basic
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.Lattice
public import Mathlib.Order.RelClasses
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.Linarith.Preprocessing
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Tactic.Ring.RingNF
public import Erdos1201.Vendor.NumberTheory.Analytic.PrimeRangeWeight
public import Erdos1201.Vendor.NumberTheory.Analytic.Mertens

@[expose] public section
namespace Analytic

open Finset

/-- An integer with no prime factor below `L`. -/
def Rough (L n : ℕ) : Prop :=
  ∀ p, p.Prime → p < L → ¬p ∣ n

theorem Rough.of_dvd {L n d : ℕ} (hn : Rough L n) (hd : d ∣ n) : Rough L d :=
  fun p hp hpL hpd => hn p hp hpL (hpd.trans hd)

/-- Classical decidability instance for `Rough`. -/
noncomputable instance roughDecidable (L n : ℕ) : Decidable (Rough L n) :=
  Classical.dec (Rough L n)

/-- Squarefree modulus formed from all primes below `L`. -/
def roughPrimeModulus (L : ℕ) : ℕ :=
  ∏ p ∈ Nat.primesBelow L, p

/-- `roughPrimeModulus L` is positive. -/
theorem roughPrimeModulus_pos (L : ℕ) :
    0 < roughPrimeModulus L := by
  unfold roughPrimeModulus
  apply Finset.prod_pos
  intro p hp
  exact (Nat.mem_primesBelow.mp hp).2.pos

/-- `n` is `L`-rough iff `n` is coprime to the squarefree modulus `roughPrimeModulus L`. -/
theorem rough_iff_coprime {L n : ℕ} :
    Rough L n ↔ (roughPrimeModulus L).Coprime n := by
  unfold roughPrimeModulus
  rw [Nat.coprime_prod_left_iff]
  constructor
  · intro h p hpMem
    have hp := Nat.mem_primesBelow.mp hpMem
    exact hp.2.coprime_iff_not_dvd.mpr (h p hp.2 hp.1)
  · intro h p hpPrime hpL
    exact hpPrime.coprime_iff_not_dvd.mp
      (h p (Nat.mem_primesBelow.mpr ⟨hpL, hpPrime⟩))

/-- Every `L`-rough integer is odd, given `L > 2`. -/
theorem odd_of_rough {L n : ℕ} (hL : 2 < L) (hn : Rough L n) :
    Odd n := by
  rw [← Nat.not_even_iff_odd]
  intro heven
  exact hn 2 Nat.prime_two hL (even_iff_two_dvd.mp heven)






/-- Euler's totient of a product of distinct primes. -/
theorem totient_primeModulus
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    (∏ p ∈ P, p).totient = ∏ p ∈ P, (p - 1) := by
  induction P using Finset.induction with
  | empty => simp
  | @insert p P hpP ih =>
      have hpPrime : p.Prime := hprime p (by simp)
      have hprimeP : ∀ q ∈ P, q.Prime := by
        intro q hq
        exact hprime q (by simp [hq])
      have hcop : p.Coprime (∏ q ∈ P, q) := by
        rw [Nat.coprime_prod_right_iff]
        intro q hq
        exact (Nat.coprime_primes hpPrime (hprimeP q hq)).2
          (by
            intro hpq
            subst q
            exact hpP hq)
      rw [prod_insert hpP, Nat.totient_mul hcop,
        Nat.totient_prime hpPrime, ih hprimeP, prod_insert hpP]

/-- Real Euler-product form of `totient_primeModulus`. -/
theorem totient_div_primeModulus_eq_product
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    (((∏ p ∈ P, p).totient : ℕ) : ℝ) / (∏ p ∈ P, p) =
      ∏ p ∈ P, (1 - (1 : ℝ) / p) := by
  rw [totient_primeModulus P hprime]
  push_cast
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hpPrime := hprime p hp
  have hp0 : (p : ℝ) ≠ 0 := by
    exact_mod_cast hpPrime.ne_zero
  rw [Nat.cast_sub hpPrime.one_le]
  field_simp
  ring

/-- A periodic coprimality condition has exactly `q * φ(a)` solutions in
an interval consisting of `q` complete periods. -/
theorem card_filter_coprime_Ico_mul
    (a k q : ℕ) :
    ((Ico k (k + a * q)).filter fun n ↦ a.Coprime n).card =
      q * a.totient := by
  induction q with
  | zero => simp
  | succ q ih =>
      have h₁ : k ≤ k + a * q := by omega
      have h₂ : k + a * q ≤ k + a * q + a := by omega
      have hend : k + a * (q + 1) = k + a * q + a := by
        simp [Nat.mul_succ, add_assoc]
      have hsplit :
          Ico k (k + a * (q + 1)) =
            Ico k (k + a * q) ∪
              Ico (k + a * q) (k + a * q + a) := by
        rw [hend]
        exact (Finset.Ico_union_Ico_eq_Ico h₁ h₂).symm
      rw [hsplit, filter_union]
      rw [card_union_of_disjoint]
      · rw [ih, Nat.filter_coprime_Ico_eq_totient]
        simp [Nat.succ_mul]
      · exact (Finset.Ico_disjoint_Ico_consecutive k
          (k + a * q) (k + a * q + a)).mono
            (filter_subset _ _) (filter_subset _ _)

/-- Lower periodic count in an arbitrary interval: discard the final
incomplete period. -/
theorem totient_mul_div_le_card_filter_coprime_Ico
    (a k n : ℕ) :
    (n / a) * a.totient ≤
      ((Ico k (k + n)).filter fun x ↦ a.Coprime x).card := by
  let q := n / a
  have hlen : a * q ≤ n := by
    dsimp [q]
    exact Nat.mul_div_le n a
  have hsub :
      (Ico k (k + a * q)).filter (fun x ↦ a.Coprime x) ⊆
        (Ico k (k + n)).filter (fun x ↦ a.Coprime x) := by
    intro x hx
    rw [mem_filter, mem_Ico] at hx ⊢
    exact ⟨⟨hx.1.1, hx.1.2.trans_le (by omega)⟩, hx.2⟩
  calc
    (n / a) * a.totient =
        ((Ico k (k + a * q)).filter fun x ↦ a.Coprime x).card := by
          symm
          simpa [q] using card_filter_coprime_Ico_mul a k q
    _ ≤ ((Ico k (k + n)).filter fun x ↦ a.Coprime x).card :=
      card_le_card hsub

/-- Real form of the periodic lower bound, with an explicit one-period
boundary loss. -/
theorem card_filter_coprime_Ico_ge_real
    {a : ℕ} (ha : 0 < a) (k n : ℕ) :
    (n : ℝ) * (a.totient : ℝ) / a - a.totient ≤
      (((Ico k (k + n)).filter fun x ↦ a.Coprime x).card : ℝ) := by
  have hnat := totient_mul_div_le_card_filter_coprime_Ico a k n
  have hcast :
      (((n / a) * a.totient : ℕ) : ℝ) ≤
        (((Ico k (k + n)).filter fun x ↦ a.Coprime x).card : ℝ) := by
    exact_mod_cast hnat
  refine le_trans ?_ hcast
  push_cast
  have hdiv : (n : ℝ) / a - 1 ≤ ((n / a : ℕ) : ℝ) := by
    have hmod : n % a < a := Nat.mod_lt n ha
    have hnlt : n < a * (n / a + 1) := by
      calc
        n = n % a + a * (n / a) := (Nat.mod_add_div n a).symm
        _ < a + a * (n / a) := Nat.add_lt_add_right hmod _
        _ = a * (n / a + 1) := by ring
    have haReal : (0 : ℝ) < a := by exact_mod_cast ha
    have hnltReal :
        (n : ℝ) < (a : ℝ) * (((n / a : ℕ) : ℝ) + 1) := by
      exact_mod_cast hnlt
    have hratio :
        (n : ℝ) / a < ((n / a : ℕ) : ℝ) + 1 :=
      (div_lt_iff₀ haReal).2 (by
        simpa [mul_comm] using hnltReal)
    linarith
  have htot : (0 : ℝ) ≤ a.totient := by positivity
  calc
    (n : ℝ) * (a.totient : ℝ) / a - a.totient =
        ((n : ℝ) / a - 1) * a.totient := by ring
    _ ≤ (n / a : ℕ) * a.totient :=
      mul_le_mul_of_nonneg_right hdiv htot

/-- Real form of the periodic upper bound, with an explicit one-period
boundary excess. -/
theorem card_filter_coprime_Ico_le_real
    {a : ℕ} (ha : a ≠ 0) (k n : ℕ) :
    (((Ico k (k + n)).filter fun x ↦ a.Coprime x).card : ℝ) ≤
      (n : ℝ) * (a.totient : ℝ) / a + a.totient := by
  have hnat :
      ((Ico k (k + n)).filter fun x ↦ a.Coprime x).card ≤
        a.totient * (n / a + 1) :=
    Nat.Ico_filter_coprime_le k n ha
  have hcast :
      (((Ico k (k + n)).filter fun x ↦ a.Coprime x).card : ℝ) ≤
        (a.totient : ℝ) * ((n / a : ℕ) + 1) := by
    exact_mod_cast hnat
  calc
    (((Ico k (k + n)).filter fun x ↦ a.Coprime x).card : ℝ) ≤
        (a.totient : ℝ) * ((n / a : ℕ) + 1) := hcast
    _ ≤ (a.totient : ℝ) * ((n : ℝ) / a + 1) := by
      gcongr
      exact Nat.cast_div_le
    _ = (n : ℝ) * (a.totient : ℝ) / a + a.totient := by ring

/-- Odd-rough integers in the source interval `[N/2, N]`. -/
noncomputable def roughSourceInterval (L N : ℕ) : Finset ℕ :=
  (Icc (N / 2) N).filter fun n ↦ Rough L n

@[simp] theorem mem_roughSourceInterval {L N n : ℕ} :
    n ∈ roughSourceInterval L N ↔
      N / 2 ≤ n ∧ n ≤ N ∧ Rough L n := by
  simp only [roughSourceInterval, mem_filter, mem_Icc]
  tauto

/-- Completely explicit positive-density lower bound for the rough source.
The density is the finite Euler product attached to the cutoff modulus. -/
theorem roughSourceInterval_card_lower
    {L N : ℕ} (hN : 4 * roughPrimeModulus L ≤ N) :
    (N : ℝ) / 4 *
        ((roughPrimeModulus L).totient : ℝ) / roughPrimeModulus L ≤
      ((roughSourceInterval L N).card : ℝ) := by
  let D := roughPrimeModulus L
  let k := N / 2
  let len := N + 1 - k
  have hD : 0 < D := roughPrimeModulus_pos L
  have hk : k ≤ N + 1 := by
    dsimp [k]
    omega
  have hend : k + len = N + 1 := by
    dsimp [len]
    omega
  have heq :
      roughSourceInterval L N =
        (Ico k (k + len)).filter fun n ↦ D.Coprime n := by
    ext n
    simp only [roughSourceInterval, mem_filter, mem_Icc, mem_Ico]
    rw [hend]
    simp only [Nat.lt_succ_iff]
    rw [rough_iff_coprime]
  have hlower :=
    card_filter_coprime_Ico_ge_real hD k len
  rw [← heq] at hlower
  have hlenReal : (N : ℝ) / 2 ≤ (len : ℝ) := by
    have hlen2Nat : N ≤ 2 * len := by
      dsimp [len, k]
      omega
    have hlen2Real : (N : ℝ) ≤ 2 * (len : ℝ) := by
      exact_mod_cast hlen2Nat
    nlinarith
  let ρ : ℝ := (D.totient : ℝ) / D
  have hρ : 0 ≤ ρ := by
    dsimp [ρ]
    positivity
  have hDρ : (D : ℝ) * ρ = D.totient := by
    dsimp [ρ]
    field_simp
  have hNreal : 4 * (D : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hN
  have hphi_le_quarter :
      (D.totient : ℝ) ≤ (N : ℝ) / 4 * ρ := by
    rw [← hDρ]
    exact mul_le_mul_of_nonneg_right (by linarith) hρ
  have hhalf :
      (N : ℝ) / 2 * ρ ≤ (len : ℝ) * ρ :=
    mul_le_mul_of_nonneg_right hlenReal hρ
  have hlower' :
      (len : ℝ) * ρ - D.totient ≤
        (roughSourceInterval L N).card := by
    (convert hlower using 1; dsimp [ρ]; ring)
  calc
    (N : ℝ) / 4 *
          ((roughPrimeModulus L).totient : ℝ) / roughPrimeModulus L =
        (N : ℝ) / 4 * ρ := by
          dsimp [ρ, D]
          ring
    _ ≤ ((roughSourceInterval L N).card : ℝ) := by
      nlinarith


/-- The density `φ(roughPrimeModulus L) / roughPrimeModulus L` equals the finite Euler product `∏_{p < L, p prime} (1 - 1/p)`. -/
theorem roughPrimeTotientDensity_eq_product (L : ℕ) :
    ((roughPrimeModulus L).totient : ℝ) / roughPrimeModulus L =
      ∏ p ∈ Nat.primesBelow L, (1 - (1 : ℝ) / p) := by
  unfold roughPrimeModulus
  exact totient_div_primeModulus_eq_product _ fun p hp ↦
    (Nat.mem_primesBelow.mp hp).2

/-- Uniform Mertens lower bound for the density of `L`-rough integers. -/
theorem mertensLowerConstant_div_log_le_roughDensity
    {L : ℕ} (hL : 3 ≤ L) :
    mertensLowerConstant / Real.log L ≤
      ((roughPrimeModulus L).totient : ℝ) / roughPrimeModulus L := by
  have hLm1 : 2 ≤ L - 1 := by omega
  have hprod :=
    mertensLowerConstant_div_log_le_primeProduct hLm1
  rw [roughPrimeTotientDensity_eq_product,
    Nat.primesBelow_eq_primesLE_sub_one]
  refine le_trans ?_ hprod
  have hlogLm1 : 0 < Real.log ((L - 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < L - 1))
  have hlogMono :
      Real.log ((L - 1 : ℕ) : ℝ) ≤ Real.log (L : ℝ) := by
    apply Real.log_le_log
    · positivity
    · exact_mod_cast Nat.sub_le L 1
  have hinv :
      1 / Real.log (L : ℝ) ≤
        1 / Real.log ((L - 1 : ℕ) : ℝ) :=
    one_div_le_one_div_of_le hlogLm1 hlogMono
  have hc : 0 ≤ mertensLowerConstant :=
    mertensLowerConstant_pos.le
  simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinv hc

end Analytic
