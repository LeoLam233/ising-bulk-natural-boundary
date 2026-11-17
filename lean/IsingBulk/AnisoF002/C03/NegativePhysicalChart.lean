import IsingBulk.AnisoF002.C03.EndpointCharts
import IsingBulk.AnisoF002.NegativeHT.LocalSpectralPhase
import IsingBulk.AnisoF002.Geometry.CanonicalRootAlgebra

/-!
# Actual physical parameter for the negative endpoint

F002 equations (4.1) and (5.1).  The local inverse and its coefficient B
are constructed from the literal spectral functions.  B is not supplied
as extra analytic data.  This file concerns the local chart and branch;
the dimension-uniform pole/density and complete coefficient tails remain
separate assertions.
-/

namespace IsingBulk.AnisoF002.Geometry
noncomputable section
open IsingBulk.Anisotropic Filter
open scoped Topology

theorem analyticAt_spectralS_f002 (z : ℂ) : AnalyticAt ℂ spectralS z :=
  Complex.analyticAt_sinh

theorem analyticAt_spectralT_f002 (lam : ℝ) (z : ℂ) :
    AnalyticAt ℂ (spectralT lam) z :=
  Complex.analyticAt_sinh.comp (analyticAt_const.mul analyticAt_id)

theorem analyticAt_spectralA_f002 (lam : ℝ) (z : ℂ) :
    AnalyticAt ℂ (spectralA lam) z :=
  Complex.analyticAt_cosh.mul
    (Complex.analyticAt_cosh.comp (analyticAt_const.mul analyticAt_id))

def spectralRatioF002 (lam : ℝ) (z : ℂ) : ℂ := spectralT lam z / spectralS z

theorem spectralT_ne_zero_of_re_ne_zero {lam : ℝ} {z : ℂ}
    (hlam : lam ≠ 0) (hx : z.re ≠ 0) : spectralT lam z ≠ 0 := by
  apply spectralS_ne_zero_of_re_ne_zero
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    using mul_ne_zero hlam hx

theorem analyticAt_spectralRatioF002 {lam : ℝ} {z : ℂ} (hS : spectralS z ≠ 0) :
    AnalyticAt ℂ (spectralRatioF002 lam) z :=
  (analyticAt_spectralT_f002 lam z).div (analyticAt_spectralS_f002 z) hS

theorem analyticAt_edgeCoordinateF002 {lam e : ℝ} {z : ℂ} (hS : spectralS z ≠ 0) :
    AnalyticAt ℂ (edgeCoordinateF002 lam e) z :=
  ((analyticAt_spectralA_f002 lam z).sub
    ((analyticAt_spectralT_f002 lam z).mul analyticAt_const)).div
    (analyticAt_spectralS_f002 z) hS

def negativeParameterF002 (lam b : ℝ) (z : ℂ) : ℂ :=
  (edgeCoordinateF002 lam (-1) z - (b : ℂ)) / spectralRatioF002 lam z

theorem negativeParameterF002_literal {lam b : ℝ} {z : ℂ}
    (hS : spectralS z ≠ 0) (hT : spectralT lam z ≠ 0) :
    negativeParameterF002 lam b z =
      (spectralA lam z / spectralS z + spectralT lam z / spectralS z - (b : ℂ)) /
        (spectralT lam z / spectralS z) := by
  unfold negativeParameterF002 edgeCoordinateF002 spectralRatioF002
  push_cast
  field_simp
  ring

theorem negativeParameterF002_center {lam b : ℝ} {z : ℂ}
    (hS : spectralS z ≠ 0)
    (hinc : spectralA lam z = spectralS z * (b : ℂ) + spectralT lam z * (-1)) :
    negativeParameterF002 lam b z = 0 := by
  unfold negativeParameterF002
  rw [edgeCoordinate_eq_of_incidence hS (by simpa using hinc), sub_self, zero_div]

theorem negativeParameterF002_hasDerivAt {lam b : ℝ} {z : ℂ}
    (hS : spectralS z ≠ 0) (hT : spectralT lam z ≠ 0)
    (hinc : spectralA lam z = spectralS z * (b : ℂ) + spectralT lam z * (-1)) :
    HasDerivAt (negativeParameterF002 lam b)
      (edgeDerivativeF002 lam (-1) z / spectralRatioF002 lam z) z := by
  have hB : spectralRatioF002 lam z ≠ 0 := div_ne_zero hT hS
  have hBa := analyticAt_spectralRatioF002 (lam := lam) hS
  have hnum : edgeCoordinateF002 lam (-1) z - (b : ℂ) = 0 := by
    rw [edgeCoordinate_eq_of_incidence hS (by simpa using hinc), sub_self]
  have hd := ((edgeCoordinate_hasDerivAt (lam := lam) (Or.inr rfl) hS).sub_const (b : ℂ)).div
    hBa.differentiableAt.hasDerivAt hB
  convert hd using 1
  · rfl
  · rw [hnum, zero_mul, sub_zero]
    field_simp

/-- A generic analytic inverse statement, proved from Mathlib's checked
inverse function theorem and retaining both local inverse identities. -/
theorem exists_local_analytic_inverse_zero {f : ℂ → ℂ} {z d : ℂ}
    (ha : AnalyticAt ℂ f z) (hd : HasDerivAt f d z) (hd0 : d ≠ 0) (hf : f z = 0) :
    ∃ Z : ℂ → ℂ, AnalyticAt ℂ Z 0 ∧ Z 0 = z ∧ HasDerivAt Z d⁻¹ 0 ∧
      (∀ᶠ t in 𝓝 0, f (Z t) = t) ∧ (∀ᶠ w in 𝓝 z, Z (f w) = w) := by
  have hstrict : HasStrictDerivAt f d z := by
    simpa only [hd.deriv] using ha.hasStrictDerivAt
  let H := (hstrict.hasStrictFDerivAt_equiv hd0).toOpenPartialHomeomorph f
  have hm : z ∈ H.source :=
    (hstrict.hasStrictFDerivAt_equiv hd0).mem_toOpenPartialHomeomorph_source
  have hZa : AnalyticAt ℂ H.symm 0 := by
    rw [← hf]
    exact H.analyticAt_symm' hm ha
      (hstrict.hasStrictFDerivAt_equiv hd0).hasFDerivAt.fderiv
  have hZ0 : H.symm 0 = z := by
    rw [← hf]
    exact H.left_inv hm
  have he : ∀ᶠ t in 𝓝 0, f (H.symm t) = t := by
    rw [← hf]
    exact H.eventually_right_inverse' hm
  have hZd : HasDerivAt H.symm d⁻¹ 0 := by
    have hh : HasDerivAt f d (H.symm 0) := by rwa [hZ0]
    exact hh.of_local_left_inverse hZa.continuousAt hd0 he
  refine ⟨H.symm, hZa, hZ0, hZd, he, ?_⟩
  exact H.eventually_left_inverse hm

theorem negative_dispersion_literal {lam b : ℝ} {z δ : ℂ}
    (hS : spectralS z ≠ 0) (hT : spectralT lam z ≠ 0) :
    (spectralA lam z - spectralT lam z * Complex.cos ((Real.pi : ℂ) + δ)) /
        spectralS z =
      (b : ℂ) + spectralRatioF002 lam z *
        (negativeParameterF002 lam b z - 1 + Complex.cos δ) := by
  rw [Complex.cos_add]
  simp only [Complex.cos_pi, Complex.sin_pi, neg_one_mul, zero_mul, sub_zero]
  unfold negativeParameterF002 edgeCoordinateF002 spectralRatioF002
  push_cast
  field_simp
  ring

theorem exists_negative_physical_chart {lam b : ℝ} {z : ℂ}
    (hlam : 0 < lam) (hx : z.re ≠ 0) (hb : |b| < 1)
    (hinc : spectralA lam z = spectralS z * (b : ℂ) + spectralT lam z * (-1)) :
    ∃ Z B : ℂ → ℂ, AnalyticAt ℂ Z 0 ∧ Z 0 = z ∧
      AnalyticAt ℂ B 0 ∧ B 0 = spectralT lam z / spectralS z ∧ B 0 ≠ 0 ∧
      (∀ t, B t = spectralT lam (Z t) / spectralS (Z t)) ∧
      (∀ᶠ t in 𝓝 0, negativeParameterF002 lam b (Z t) = t ∧
        spectralS (Z t) ≠ 0 ∧ spectralT lam (Z t) ≠ 0 ∧
        ∀ δ : ℂ,
          (spectralA lam (Z t) - spectralT lam (Z t) *
            Complex.cos ((Real.pi : ℂ) + δ)) / spectralS (Z t) =
            (b : ℂ) + B t * (t - 1 + Complex.cos δ)) ∧
      (∀ᶠ w in 𝓝 z, Z (negativeParameterF002 lam b w) = w) := by
  have hS := spectralS_ne_zero_of_re_ne_zero hx
  have hT := spectralT_ne_zero_of_re_ne_zero (ne_of_gt hlam) hx
  have hB0 : spectralRatioF002 lam z ≠ 0 := div_ne_zero hT hS
  have hBa := analyticAt_spectralRatioF002 (lam := lam) hS
  have hta : AnalyticAt ℂ (negativeParameterF002 lam b) z :=
    ((analyticAt_edgeCoordinateF002 (e := -1) hS).sub analyticAt_const).div hBa hB0
  have htd := negativeParameterF002_hasDerivAt hS hT hinc
  have htd0 : edgeDerivativeF002 lam (-1) z / spectralRatioF002 lam z ≠ 0 :=
    div_ne_zero (edgeDerivative_ne_zero_all_re hlam hx hb (Or.inr rfl)
      (by simpa using hinc)) hB0
  obtain ⟨Z, hZa, hZ0, _, hright, hleft⟩ :=
    exists_local_analytic_inverse_zero hta htd htd0
      (negativeParameterF002_center hS hinc)
  let B : ℂ → ℂ := fun t => spectralRatioF002 lam (Z t)
  have hBa' : AnalyticAt ℂ B 0 := hBa.comp_of_eq hZa hZ0
  have hB0' : B 0 = spectralT lam z / spectralS z := by simp only [B, hZ0, spectralRatioF002]
  refine ⟨Z, B, hZa, hZ0, hBa', hB0', ?_, fun _ => rfl, ?_, hleft⟩
  · rw [hB0']
    exact div_ne_zero hT hS
  · have hS' : ∀ᶠ t in 𝓝 0, spectralS (Z t) ≠ 0 :=
      ((analyticAt_spectralS_f002 z).comp_of_eq hZa hZ0).continuousAt.eventually_ne
        (by simpa only [Function.comp_def, hZ0] using hS)
    have hT' : ∀ᶠ t in 𝓝 0, spectralT lam (Z t) ≠ 0 :=
      ((analyticAt_spectralT_f002 lam z).comp_of_eq hZa hZ0).continuousAt.eventually_ne
        (by simpa only [Function.comp_def, hZ0] using hT)
    filter_upwards [hright, hS', hT'] with t ht hs ht'
    refine ⟨ht, hs, ht', fun δ => ?_⟩
    rw [negative_dispersion_literal hs ht', ht]

end
end IsingBulk.AnisoF002.Geometry
