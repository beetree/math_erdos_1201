import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# The arithmetic denominator in the corrected Ramaré identity

The original paper and proof for Erdős Problem #1201 are by Przemek Chojecki together
with ChatGPT 5.5 (`erdos1201.pdf`).

These auxiliary lemmas are adapted from the user-supplied incomplete expert
Matomäki–Radziwiłł formalization (based on Section 5, equation 16 of arXiv:1501.04585v4).
These lemmas DO NOT prove `QuantitativeShortIntervalInput`.

The argument applies to an arbitrary finite set of primes, not merely primes in an interval.
-/

namespace Erdos1201.MR

/-- Distinct prime divisors selected from a finite set. Primality is a hypothesis
of the theorems, not part of this definition. -/
def divisorsIn (S : Finset ℕ) (n : ℕ) : Finset ℕ :=
  S.filter (fun p => p ∣ n)

/-- The number of selected distinct prime divisors, not the number with multiplicity. -/
def omegaIn (S : Finset ℕ) (n : ℕ) : ℕ :=
  (divisorsIn S n).card

/-- Denominator in equation (16), using `p ∤ m` for prime `p`. -/
def correctedCount (S : Finset ℕ) (p m : ℕ) : ℕ :=
  omegaIn S m + if p ∣ m then 0 else 1

@[simp] theorem mem_divisorsIn {S : Finset ℕ} {n p : ℕ} :
    p ∈ divisorsIn S n ↔ p ∈ S ∧ p ∣ n := by
  simp [divisorsIn]

/-- Multiplication by a selected prime inserts exactly that prime in the set
of selected distinct divisors. This also covers `p ∣ m`. -/
theorem divisorsIn_prime_mul {S : Finset ℕ} {p m : ℕ}
    (hS : ∀ q ∈ S, Nat.Prime q) (hp : p ∈ S) :
    divisorsIn S (p * m) = insert p (divisorsIn S m) := by
  classical
  ext q
  simp only [mem_divisorsIn, Finset.mem_insert]
  constructor
  · rintro ⟨hq, hdiv⟩
    rcases (hS q hq).dvd_mul.mp hdiv with hqp | hqm
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq (hS q hq) (hS p hp)).mp hqp)
    · exact Or.inr ⟨hq, hqm⟩
  · rintro (rfl | ⟨hq, hqm⟩)
    · exact ⟨hp, ⟨m, rfl⟩⟩
    · refine ⟨hq, ?_⟩
      obtain ⟨k, hk⟩ := hqm
      refine ⟨p * k, ?_⟩
      rw [hk]
      ring

/-- The indicator is essential: the count increases only when `p ∤ m`. -/
theorem omegaIn_prime_mul {S : Finset ℕ} {p m : ℕ}
    (hS : ∀ q ∈ S, Nat.Prime q) (hp : p ∈ S) :
    omegaIn S (p * m) = correctedCount S p m := by
  classical
  change (divisorsIn S (p * m)).card =
    (divisorsIn S m).card + if p ∣ m then 0 else 1
  rw [divisorsIn_prime_mul hS hp]
  by_cases hpm : p ∣ m
  · have hmem : p ∈ divisorsIn S m := mem_divisorsIn.mpr ⟨hp, hpm⟩
    simp [hpm, Finset.card_insert_of_mem hmem]
  · have hnot : p ∉ divisorsIn S m := by
      simpa only [mem_divisorsIn, hp, true_and] using hpm
    simp [hpm, Finset.card_insert_of_notMem hnot]

/-- For a prime divisor of `n`, the corrected denominator after removing that
prime is exactly the original number of selected prime divisors. -/
theorem correctedCount_div {S : Finset ℕ} {p n : ℕ}
    (hS : ∀ q ∈ S, Nat.Prime q) (hp : p ∈ S) (hpn : p ∣ n) :
    correctedCount S p (n / p) = omegaIn S n := by
  calc
    correctedCount S p (n / p) = omegaIn S (p * (n / p)) :=
      (omegaIn_prime_mul hS hp).symm
    _ = omegaIn S n := by rw [Nat.mul_div_cancel' hpn]

theorem omegaIn_pos_of_selected_dvd {S : Finset ℕ} {p n : ℕ}
    (hp : p ∈ S) (hpn : p ∣ n) :
    0 < omegaIn S n := by
  exact Finset.card_pos.mpr ⟨p, mem_divisorsIn.mpr ⟨hp, hpn⟩⟩

/-- No division by zero occurs in a summand of the Ramaré decomposition. -/
theorem correctedCount_div_pos {S : Finset ℕ} {p n : ℕ}
    (hS : ∀ q ∈ S, Nat.Prime q) (hp : p ∈ S) (hpn : p ∣ n) :
    0 < correctedCount S p (n / p) := by
  rw [correctedCount_div hS hp hpn]
  exact omegaIn_pos_of_selected_dvd hp hpn

/-- Agreement with the authors' coprimality-indicator notation. -/
theorem correctedCount_eq_coprime {S : Finset ℕ} {p m : ℕ}
    (hp : Nat.Prime p) :
    correctedCount S p m = omegaIn S m + if Nat.Coprime p m then 1 else 0 := by
  unfold correctedCount
  by_cases hpm : p ∣ m
  · have hnot : ¬Nat.Coprime p m := by
      intro hcop
      exact (hp.coprime_iff_not_dvd.mp hcop) hpm
    simp [hpm, hnot]
  · have hcop : Nat.Coprime p m := hp.coprime_iff_not_dvd.mpr hpm
    simp [hpm, hcop]

/-- The terms needing a correction are supported on prime-square divisors. -/
theorem square_dvd_of_dvd_quotient {p n : ℕ}
    (hpn : p ∣ n) (hquot : p ∣ n / p) :
    p ^ 2 ∣ n := by
  obtain ⟨k, hk⟩ := hquot
  refine ⟨k, ?_⟩
  calc
    n = p * (n / p) := (Nat.mul_div_cancel' hpn).symm
    _ = p * (p * k) := by rw [hk]
    _ = p ^ 2 * k := by ring

/-- A square-free-in-`S` condition removes all correction terms. -/
theorem not_dvd_quotient_of_not_square_dvd {p n : ℕ}
    (hpn : p ∣ n) (hsq : ¬p ^ 2 ∣ n) :
    ¬p ∣ n / p := by
  intro hquot
  exact hsq (square_dvd_of_dvd_quotient hpn hquot)

/-- Regression case from the published denominator error: `4 = 2 * 2`. -/
example : omegaIn {2} 4 = 1 := by
  decide

example : correctedCount {2} 2 2 = 1 := by
  decide

example : omegaIn {2} 2 + 1 = 2 := by
  decide

end Erdos1201.MR
