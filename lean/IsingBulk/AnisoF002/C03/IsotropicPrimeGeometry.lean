import IsingBulk.AnisoF002.C03.IsotropicPrimeExclusion
import IsingBulk.AnisoF002.C03.IsotropicBranchArithmetic

/-!
# Actual prime angles and the absence of lower Nickel points

The cyclotomic arguments are specialized to the exact real cosine grids
in the frozen F002 proof.  Both signs needed for the branch-mean gap are
realized by explicit primitive roots.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section

def isotropicPrimeAngle (p a : ℕ) : ℝ := 2 * Real.pi * a / p

def isotropicPrimeRoot (p a : ℕ) : ℂ :=
  Complex.exp ((isotropicPrimeAngle p a : ℂ) * Complex.I)

theorem isotropicPrimeRoot_primitive {p a : ℕ} (hp : 0 < p) (ha : a.Coprime p) :
    IsPrimitiveRoot (isotropicPrimeRoot p a) p := by
  have he : (isotropicPrimeAngle p a : ℂ) * Complex.I =
      2 * Real.pi * Complex.I * ((a : ℂ) / p) := by
    simp only [isotropicPrimeAngle, Complex.ofReal_div, Complex.ofReal_mul,
      Complex.ofReal_natCast, Complex.ofReal_ofNat]
    ring
  rw [isotropicPrimeRoot, he]
  exact Complex.isPrimitiveRoot_exp_of_coprime a p hp.ne' ha

theorem isotropicPrimeRoot_pow (p a : ℕ) (hp : 0 < p) :
    isotropicPrimeRoot p a ^ p = 1 := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [isotropicPrimeRoot, ← Complex.exp_nat_mul]
  convert Complex.exp_nat_mul_two_pi_mul_I a using 1
  congr 1
  simp only [isotropicPrimeAngle, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_natCast, Complex.ofReal_ofNat]
  field_simp

theorem isotropicPrimeRoot_trace (p a : ℕ) :
    isotropicPrimeRoot p a + (isotropicPrimeRoot p a)⁻¹ =
      (2 * Real.cos (isotropicPrimeAngle p a) : ℝ) := by
  rw [isotropicPrimeRoot, ← Complex.exp_neg]
  rw [show -((isotropicPrimeAngle p a : ℂ) * Complex.I) =
    ((-isotropicPrimeAngle p a : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg, Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  ring

theorem isotropic_prime_angle_nickel_exclusion {p a n : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (ha : a.Coprime p) (hn : 0 < n)
    (hpn : ¬ p ∣ n) (l m : ℕ) :
    2 * Real.cos (isotropicPrimeAngle p a) ≠
      Real.cos (isotropicPrimeAngle n l) + Real.cos (isotropicPrimeAngle n m) := by
  intro he
  apply isotropic_prime_trace_not_competitors hp hp5 hn hpn
    (isotropicPrimeRoot_primitive hp.pos ha)
    (isotropicPrimeRoot_pow n l hn) (isotropicPrimeRoot_pow n m hn)
  rw [isotropicPrimeRoot_trace, isotropicPrimeRoot_trace, isotropicPrimeRoot_trace]
  push_cast
  have hc := congrArg (fun r : ℝ => (r : ℂ)) he
  push_cast at hc
  linear_combination 2 * hc

theorem exists_isotropic_positive_primitive_trace {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) :
    ∃ y : ℂ, IsPrimitiveRoot y p ∧ 0 < (y + y⁻¹).re := by
  refine ⟨isotropicPrimeRoot p 1, isotropicPrimeRoot_primitive hp.pos (Nat.coprime_one_left p), ?_⟩
  rw [isotropicPrimeRoot_trace, Complex.ofReal_re]
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hp4 : 4 < (p : ℝ) := by exact_mod_cast (by omega : 4 < p)
  have ha0 : 0 < isotropicPrimeAngle p 1 := by
    simp only [isotropicPrimeAngle, Nat.cast_one, mul_one]
    exact div_pos (by positivity) hpR
  have ha1 : isotropicPrimeAngle p 1 < Real.pi / 2 := by
    rw [isotropicPrimeAngle, Nat.cast_one, mul_one, div_lt_iff₀ hpR]
    nlinarith [Real.pi_pos]
  have hc := Real.cos_pos_of_mem_Ioo
    (show isotropicPrimeAngle p 1 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) from
      ⟨by linarith [Real.pi_pos], ha1⟩)
  positivity

theorem exists_isotropic_negative_primitive_trace {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) :
    ∃ y : ℂ, IsPrimitiveRoot y p ∧ (y + y⁻¹).re < 0 := by
  obtain ⟨d, hd⟩ := hp.odd_of_ne_two (by omega)
  have hd0 : 0 < d := by omega
  have hdp : d < p := by omega
  have hdc : d.Coprime p := (hp.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt hd0 hdp)).symm
  refine ⟨isotropicPrimeRoot p d, isotropicPrimeRoot_primitive hp.pos hdc, ?_⟩
  rw [isotropicPrimeRoot_trace, Complex.ofReal_re]
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hdR : (p : ℝ) = 2 * (d : ℝ) + 1 := by exact_mod_cast hd
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast (by omega : 2 ≤ d)
  have hlo : Real.pi / 2 < isotropicPrimeAngle p d := by
    rw [isotropicPrimeAngle, lt_div_iff₀ hpR]
    nlinarith [Real.pi_pos]
  have hhi : isotropicPrimeAngle p d < Real.pi := by
    rw [isotropicPrimeAngle, div_lt_iff₀ hpR]
    nlinarith [Real.pi_pos]
  have hc := Real.cos_neg_of_pi_div_two_lt_of_lt hlo
    (show isotropicPrimeAngle p d < Real.pi + Real.pi / 2 by linarith [Real.pi_pos])
  linarith

end
end IsingBulk.AnisoF002.Isotropic
