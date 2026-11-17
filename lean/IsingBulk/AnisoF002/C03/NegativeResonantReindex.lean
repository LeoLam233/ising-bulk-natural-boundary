import IsingBulk.AnisoF002.C03.NegativeFullTaylorExtraction
import IsingBulk.AnisoF002.C03.NegativeParticleWindow
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Exact rational resonance and complete physical residue reindexing

Coprimality proves the minimal phase period.  Every nonzero physical
residue is then retained by the single progression p(2q+1), and every
index of that progression occurs once.  This is an equality of the
whole infinite residue sums, not a restriction of the physical series.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open scoped BigOperators

theorem rational_negative_phase_resonance_iff {r p : ℕ} (hp : p ≠ 0)
    (hcop : r.Coprime p) (N : ℕ) :
    Complex.exp (-((N : ℂ) * (((2 * Real.pi * r / p : ℝ) : ℂ) * Complex.I))) = 1 ↔
      p ∣ N := by
  have hprimitive := (Complex.isPrimitiveRoot_exp_of_coprime r p hp hcop).inv
  have hid : Complex.exp (-((N : ℂ) * (((2 * Real.pi * r / p : ℝ) : ℂ) * Complex.I))) =
      ((Complex.exp (2 * Real.pi * Complex.I * ((r : ℂ) / p)))⁻¹) ^ N := by
    rw [← Complex.exp_neg, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hid]
  exact hprimitive.pow_eq_one_iff_dvd N

def resonantOddIndex (p q : ℕ) : ℕ := p * q + p / 2

theorem resonantOddIndex_particle {p : ℕ} (hp : Odd p) (q : ℕ) :
    2 * resonantOddIndex p q + 1 = resonantParticleCount p q := by
  have hh := Nat.two_mul_div_two_add_one_of_odd hp
  unfold resonantOddIndex resonantParticleCount
  nlinarith

theorem resonantOddIndex_injective {p : ℕ} (hp : 0 < p) :
    Function.Injective (resonantOddIndex p) := by
  have hh : StrictMono (resonantOddIndex p) := by
    intro a b hab
    exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_left hab hp) (p / 2)
  exact hh.injective

theorem exists_resonantOddIndex_iff {p n : ℕ} (hp : Odd p) :
    (∃ q : ℕ, resonantOddIndex p q = n) ↔ p ∣ 2 * n + 1 := by
  constructor
  · rintro ⟨q, rfl⟩
    rw [resonantOddIndex_particle hp]
    exact ⟨2 * q + 1, rfl⟩
  · rintro ⟨k, hk⟩
    have hodd : Odd k := Nat.Odd.of_mul_right (hk ▸ (show Odd (2 * n + 1) from ⟨n, rfl⟩))
    obtain ⟨q, hq⟩ := hodd
    have hkq : k = 2 * q + 1 := by omega
    have hcount : resonantParticleCount p q = 2 * n + 1 := by
      unfold resonantParticleCount
      rw [← hkq, ← hk]
    have hh := (resonantOddIndex_particle hp q).trans hcount
    exact ⟨q, by omega⟩

theorem completeCyclePoleCoefficient_tsum_resonant {b B : ℂ → ℂ}
    {φ radius cutoff M kappa : ℝ} {r p : ℕ} (hp : Odd p) (hcop : r.Coprime p)
    (hφ : φ = 2 * Real.pi * r / p)
    (D : ∀ n : ℕ, InnerRemainderFamily b B φ (2 * n + 1) radius cutoff M kappa)
    (j : ℕ) :
    (∑' n : ℕ, completeCyclePoleCoefficient D j n) =
      ∑' q : ℕ, innerCyclePoleCoefficient (D (resonantOddIndex p q)) j := by
  have hphase (N : ℕ) :
      Complex.exp (-((N : ℂ) * ((φ : ℂ) * Complex.I))) = 1 ↔ p ∣ N := by
    rw [hφ]
    exact rational_negative_phase_resonance_iff hp.pos.ne' hcop N
  have hsupport : Function.support (completeCyclePoleCoefficient D j) ⊆
      Set.range (resonantOddIndex p) := by
    intro n hn
    change completeCyclePoleCoefficient D j n ≠ 0 at hn
    have hr : Complex.exp (-(((2 * n + 1 : ℕ) : ℂ) * ((φ : ℂ) * Complex.I))) = 1 := by
      by_contra hh
      simp only [completeCyclePoleCoefficient, hh, ↓reduceIte, ne_eq, not_true_eq_false] at hn
    exact (exists_resonantOddIndex_iff hp).mpr ((hphase (2 * n + 1)).mp hr)
  rw [← (resonantOddIndex_injective hp.pos).tsum_eq hsupport]
  apply tsum_congr
  intro q
  have hdiv : p ∣ 2 * resonantOddIndex p q + 1 :=
    (exists_resonantOddIndex_iff hp).mp ⟨q, rfl⟩
  have hr := (hphase (2 * resonantOddIndex p q + 1)).mpr hdiv
  simp only [completeCyclePoleCoefficient, hr, ↓reduceIte]

end
end IsingBulk.AnisoF002.NegativeHT
