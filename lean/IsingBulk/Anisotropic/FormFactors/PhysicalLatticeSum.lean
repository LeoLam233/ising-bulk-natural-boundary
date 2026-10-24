import IsingBulk.Anisotropic.FormFactors.LatticeReflection
import IsingBulk.Anisotropic.FormFactors.RadiusIndependence

namespace IsingBulk.Anisotropic.FormFactors
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour
open scoped BigOperators

theorem physical_margin_contourAnnulus {lam x r : ℝ} (hlam : 0 < lam) (hx : 0 < x)
    (hr : 0 < r) (hr1 : r < 1)
    (hm : (realB lam x+1)*(1+r⁻¹)/2 < realC lam x) :
    ContourAnnulus lam (x:ℂ) r := by
  refine ⟨hr,hr1,?_⟩
  intro u y hu hu1 hy hy1
  rw [physical_dispersion_scale hx]
  apply mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sinh_pos_iff.mpr hx).ne')
  have hp := realContourDispersion_re_pos (realB_pos hlam hx).le hr hm hu hu1 hy hy1
  intro he
  rw [he,Complex.zero_re] at hp
  exact (lt_irrefl 0) hp

theorem physical_temperatureScale {lam x : ℝ} (hlam : 0 < lam) (hx : 0 < x) :
    Real.sinh x*Real.sqrt (realB lam x) = Real.sqrt (realProduct lam x) := by
  have hS := Real.sinh_pos_iff.mpr hx
  have hT := Real.sinh_pos_iff.mpr (mul_pos hlam hx)
  have hB := realB_pos hlam hx
  have hp : 0 < realProduct lam x := mul_pos hS hT
  have hsquare : (Real.sinh x*Real.sqrt (realB lam x))^2 = realProduct lam x := by
    rw [mul_pow,Real.sq_sqrt hB.le]
    unfold realB realProduct
    field_simp
  nlinarith [Real.sq_sqrt hp.le,Real.sqrt_nonneg (realProduct lam x),
    mul_nonneg hS.le (Real.sqrt_nonneg (realB lam x))]

theorem physical_latticeCoefficient_eq_double_contour (N : ℕ) {lam x r : ℝ}
    (hlam : 0 < lam) (hx : 0 < x) (hp : realProduct lam x ≠ 1)
    (hr : 0 < r) (hr1 : r < 1)
    (hm : (realB lam x+1)*(1+r⁻¹)/2 < realC lam x) (v : ℤ × ℤ) :
    latticeCoefficient N (realB lam x) (realC lam x) v =
      ((Real.sqrt (realProduct lam x))^N:ℝ)*unscaledLatticeCoefficientAtRadius N r lam (x:ℂ) v := by
  rw [latticeCoefficient_eq_unit_contour N (realB_pos hlam hx) (real_dispersion_gap hlam hx hp)
    (Real.sinh_pos_iff.mpr hx).ne',physical_temperatureScale hlam hx,
    unscaledLatticeCoefficient_eq_canceled_unit N hlam hx hr hr1 hm v]
  simp only [spectralS,← Complex.ofReal_sinh]
  ring

/-- Absolute all-site summability and the exact full coefficient attachment.
The particle-number sum is not interchanged in this theorem. -/
theorem physical_lattice_summable_eq_full (N : ℕ) (hN : 0 < N) {lam x : ℝ}
    (hlam : 0 < lam) (hx : 0 < x) (hp : realProduct lam x ≠ 1) :
    Summable (fun v : ℤ × ℤ => ‖latticeCoefficient N (realB lam x) (realC lam x) v‖) ∧
    (∑' v : ℤ × ℤ, latticeCoefficient N (realB lam x) (realC lam x) v) =
      ((Real.sqrt (realProduct lam x))^N:ℝ)*unscaledFullCoefficient N lam (x:ℂ) := by
  obtain ⟨r,hr,hr1,hm⟩ := physical_margin_radius (realB_pos hlam hx).le (real_dispersion_gap hlam hx hp)
  have ha := physical_margin_contourAnnulus hlam hx hr hr1 hm
  have he := physical_latticeCoefficient_eq_double_contour N hlam hx hp hr hr1 hm
  obtain ⟨hs,ht⟩ := unscaledLattice_summable_eq_full N hN ha
  have hc : unscaledFullCoefficient N lam (x:ℂ) = unscaledFullCoefficientAtRadius N r lam (x:ℂ) :=
    unscaledFullCoefficient_radius_independent N hN (contourRadius_spec ⟨r,ha⟩) ha
  constructor
  · simp_rw [he,norm_mul]
    exact hs.mul_left _
  · simp_rw [he]
    rw [tsum_mul_left,ht,hc]
end
end IsingBulk.Anisotropic.FormFactors
