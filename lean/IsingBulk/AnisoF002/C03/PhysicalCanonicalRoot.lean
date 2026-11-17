import IsingBulk.AnisoF002.Geometry.CanonicalRootContinuity
import IsingBulk.AnisoF002.C03.RegularEdgeJointDensity

/-!
# The canonical complex-angle root and its filled quotient by S

The choice is the same strict-disk solution of the unsquared quadratic.
The quotient r/S is filled as (2C-Sr)^{-1}; that denominator cannot vanish
on a nondegenerate spectral fibre, including S=0.  This supplies the
actual global angular normalization without a punctured domain or an
extra square-root branch assumption.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open IsingBulk.Anisotropic IsingBulk.AnisoF002.Geometry Filter Set
open scoped Topology BigOperators

def physicalQuadraticRoot (a : ℂ × ℂ) : ℂ := by
  classical
  exact if h : ∃ r : ℂ, a.1 * r ^ 2 - 2 * a.2 * r + a.1 = 0 ∧ ‖r‖ < 1 then h.choose else 0

theorem physicalQuadraticRoot_spec {a : ℂ × ℂ}
    (he : ∃ r : ℂ, a.1 * r ^ 2 - 2 * a.2 * r + a.1 = 0 ∧ ‖r‖ < 1) :
    a.1 * physicalQuadraticRoot a ^ 2 - 2 * a.2 * physicalQuadraticRoot a + a.1 = 0 ∧
      ‖physicalQuadraticRoot a‖ < 1 := by
  simp only [physicalQuadraticRoot, dite_eq_left he]
  exact he.choose_spec

theorem physicalQuadraticRoot_unique {S C r s : ℂ} (hSC : S ≠ 0 ∨ C ≠ 0)
    (hr : S * r ^ 2 - 2 * C * r + S = 0)
    (hs : S * s ^ 2 - 2 * C * s + S = 0) (hnr : ‖r‖ < 1) (hns : ‖s‖ < 1) : r = s := by
  by_cases hS : S = 0
  · have hC := hSC.resolve_left (not_not.mpr hS)
    have hr0 : r = 0 := by
      have hh : (2 * C) * r = 0 := by simpa only [hS, zero_mul, zero_sub, add_zero, neg_eq_zero] using hr
      exact (mul_eq_zero.mp hh).resolve_left (mul_ne_zero (by norm_num) hC)
    have hs0 : s = 0 := by
      have hh : (2 * C) * s = 0 := by simpa only [hS, zero_mul, zero_sub, add_zero, neg_eq_zero] using hs
      exact (mul_eq_zero.mp hh).resolve_left (mul_ne_zero (by norm_num) hC)
    exact hr0.trans hs0.symm
  · have hf : S * ((r - s) * (r * s - 1)) = 0 := by
      linear_combination s * hr - r * hs
    rcases mul_eq_zero.mp ((mul_eq_zero.mp hf).resolve_left hS) with h | h
    · exact sub_eq_zero.mp h
    · have hp := congrArg norm (sub_eq_zero.mp h)
      simp only [norm_mul, norm_one] at hp
      have hlt : ‖r‖ * ‖s‖ < 1 :=
        (mul_le_mul_of_nonneg_left hns.le (norm_nonneg r)).trans_lt (by simpa using hnr)
      linarith

theorem physicalQuadraticRoot_analyticAt {a : ℂ × ℂ} (hSC : a.1 ≠ 0 ∨ a.2 ≠ 0)
    (he : ∃ r : ℂ, a.1 * r ^ 2 - 2 * a.2 * r + a.1 = 0 ∧ ‖r‖ < 1) :
    AnalyticAt ℂ physicalQuadraticRoot a := by
  have hs := physicalQuadraticRoot_spec he
  obtain ⟨R, hR, _, hnear⟩ := exists_joint_analytic_quadratic_root
    a.1 a.2 (physicalQuadraticRoot a) hs.1 (quadratic_small_root_simple hSC hs.1 hs.2) hs.2
  have hSCnear : ∀ᶠ b : ℂ × ℂ in 𝓝 a, b.1 ≠ 0 ∨ b.2 ≠ 0 := by
    rcases hSC with hS | hC
    · exact (continuousAt_fst.eventually_ne hS).mono (fun _ h => Or.inl h)
    · exact (continuousAt_snd.eventually_ne hC).mono (fun _ h => Or.inr h)
  apply hR.congr
  filter_upwards [hnear, hSCnear] with b hb hbc
  have hh := physicalQuadraticRoot_spec (show ∃ r : ℂ,
      b.1 * r ^ 2 - 2 * b.2 * r + b.1 = 0 ∧ ‖r‖ < 1 from ⟨R b, hb⟩)
  exact physicalQuadraticRoot_unique hbc hb.1 hh.1 hb.2 hh.2

theorem physical_quadratic_quotient_denominator {S C r : ℂ} (hSC : S ≠ 0 ∨ C ≠ 0)
    (hp : S * r ^ 2 - 2 * C * r + S = 0) : 2 * C - S * r ≠ 0 := by
  intro hd
  have hS : S = 0 := by linear_combination hp + r * hd
  have hC : C = 0 := by simpa only [hS, zero_mul, sub_zero, mul_eq_zero, OfNat.ofNat_ne_zero, false_or] using hd
  exact hSC.elim (fun h => h hS) (fun h => h hC)

theorem physical_quadratic_root_quotient {S C r : ℂ} (hSC : S ≠ 0 ∨ C ≠ 0)
    (hp : S * r ^ 2 - 2 * C * r + S = 0) : S * (2 * C - S * r)⁻¹ = r := by
  have hd := physical_quadratic_quotient_denominator hSC hp
  apply (mul_right_cancel₀ hd)
  rw [mul_assoc, inv_mul_cancel₀ hd, mul_one]
  linear_combination hp

def physicalComplexRoot (lam : ℝ) (p : ℂ × ℂ) : ℂ :=
  physicalQuadraticRoot (spectralCoefficientsF002 lam p)

def physicalRootQuotient (lam : ℝ) (p : ℂ × ℂ) : ℂ :=
  (2 * (spectralA lam p.1 - spectralT lam p.1 * Complex.cos p.2) -
    spectralS p.1 * physicalComplexRoot lam p)⁻¹

theorem physicalComplexRoot_real {lam : ℝ} {z : ℂ} (q : ℝ)
    (hz : z ∉ spectralSetF002 lam) :
    physicalComplexRoot lam (z, (q : ℂ)) = spectralSmallRootF002 lam z q := by
  have hs := spectralSmallRootF002_spec q hz
  have he : ∃ r : ℂ,
      (spectralCoefficientsF002 lam (z, (q : ℂ))).1 * r ^ 2 -
        2 * (spectralCoefficientsF002 lam (z, (q : ℂ))).2 * r +
        (spectralCoefficientsF002 lam (z, (q : ℂ))).1 = 0 ∧ ‖r‖ < 1 := by
    refine ⟨spectralSmallRootF002 lam z q, ?_, hs.2⟩
    simpa only [spectralCoefficientsF002, ← Complex.ofReal_cos, spectralRootPolynomialF002] using hs.1
  apply spectralSmallRootF002_unique q hz
  · simpa only [physicalComplexRoot, spectralCoefficientsF002, ← Complex.ofReal_cos,
      spectralRootPolynomialF002] using (physicalQuadraticRoot_spec he).1
  · exact (physicalQuadraticRoot_spec he).2

theorem physicalComplexRoot_analyticAt {lam : ℝ} {z : ℂ} (q : ℝ)
    (hz : z ∉ spectralSetF002 lam) : AnalyticAt ℂ (physicalComplexRoot lam) (z, (q : ℂ)) := by
  have hs := spectralSmallRootF002_spec q hz
  apply (physicalQuadraticRoot_analyticAt ?_ ?_).comp (spectralCoefficientsF002_analyticAt lam _)
  · simpa only [spectralCoefficientsF002, ← Complex.ofReal_cos] using spectral_coefficients_nondegenerate q hz
  · refine ⟨spectralSmallRootF002 lam z q, ?_, hs.2⟩
    simpa only [spectralCoefficientsF002, ← Complex.ofReal_cos, spectralRootPolynomialF002] using hs.1

theorem physicalRootQuotient_denominator {lam : ℝ} {z : ℂ} (q : ℝ)
    (hz : z ∉ spectralSetF002 lam) :
    2 * (spectralA lam z - spectralT lam z * Complex.cos (q : ℂ)) -
      spectralS z * physicalComplexRoot lam (z, (q : ℂ)) ≠ 0 := by
  rw [physicalComplexRoot_real q hz, ← Complex.ofReal_cos]
  exact physical_quadratic_quotient_denominator (spectral_coefficients_nondegenerate q hz)
    (spectralSmallRootF002_spec q hz).1

theorem physicalRootQuotient_analyticAt {lam : ℝ} {z : ℂ} (q : ℝ)
    (hz : z ∉ spectralSetF002 lam) : AnalyticAt ℂ (physicalRootQuotient lam) (z, (q : ℂ)) := by
  have ha := spectralCoefficientsF002_analyticAt lam (z, (q : ℂ))
  have hS : AnalyticAt ℂ (fun p : ℂ × ℂ => spectralS p.1) (z, (q : ℂ)) :=
    analyticAt_fst.comp ha
  have hC : AnalyticAt ℂ (fun p : ℂ × ℂ =>
      spectralA lam p.1 - spectralT lam p.1 * Complex.cos p.2) (z, (q : ℂ)) :=
    analyticAt_snd.comp ha
  exact ((analyticAt_const.mul hC).sub (hS.mul (physicalComplexRoot_analyticAt q hz))).inv
    (physicalRootQuotient_denominator q hz)

theorem physicalRootQuotient_mul_spectralS {lam : ℝ} {z : ℂ} (q : ℝ)
    (hz : z ∉ spectralSetF002 lam) :
    spectralS z * physicalRootQuotient lam (z, (q : ℂ)) = spectralSmallRootF002 lam z q := by
  unfold physicalRootQuotient
  rw [physicalComplexRoot_real q hz, ← Complex.ofReal_cos]
  exact physical_quadratic_root_quotient (spectral_coefficients_nondegenerate q hz)
    (spectralSmallRootF002_spec q hz).1

end
end IsingBulk.AnisoF002.RegularTail.C03
