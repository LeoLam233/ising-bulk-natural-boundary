import IsingBulk.Anisotropic.FormFactors.CanceledLattice

namespace IsingBulk.Anisotropic.FormFactors
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour

theorem realContourRoot_unit {B C : ℝ} (hB : 0 ≤ B) (hgap : 1 < C-B) (q : ℝ) :
    realContourRoot B C (limitingAngle q) = (root B C q:ℂ) := by
  have hw : realContourW B C (limitingAngle q) = (C-B*Real.cos q:ℝ) := by
    unfold realContourW
    rw [limitingAngle_trace]
    push_cast
    ring
  unfold realContourRoot
  rw [hw,compactLeftRoot_eq_exp_neg_arcosh (dispersion_gt_one hB hgap q)]
  rfl

theorem physical_dispersion_scale {lam x : ℝ} (hx : 0 < x) (u y : ℂ) :
    sliceDispersion lam (x:ℂ) u y = (Real.sinh x:ℂ)*
      realContourDispersion (realB lam x) (realC lam x) u y := by
  have hS : (Real.sinh x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sinh_pos_iff.mpr hx).ne'
  unfold sliceDispersion dispersionPolynomial realContourDispersion realContourW realB realC
    spectralA spectralS spectralT
  simp only [← Complex.ofReal_mul,← Complex.ofReal_cosh,← Complex.ofReal_sinh,Complex.ofReal_div]
  field_simp
  ring

theorem realContourRoot_physical_equation {lam x : ℝ} (hx : 0 < x) (y : ℂ) :
    RootEquation lam (x:ℂ) y (realContourRoot (realB lam x) (realC lam x) y) := by
  have hz := physical_dispersion_scale (lam := lam) hx (realContourRoot (realB lam x) (realC lam x) y) y
  rw [realContourRoot_dispersion,mul_zero] at hz
  unfold sliceDispersion dispersionPolynomial at hz
  unfold RootEquation
  linear_combination hz

/-- The outer contour moves through the collision-canceled expression,
never through an uncanceled pole at a reciprocal pair on the unit circle. -/
theorem canceledLattice_unit_contour_eq_radius (N : ℕ) {B C r : ℝ} {S : ℂ}
    (hB : 0 ≤ B) (hS : S ≠ 0) (hr : 0 < r) (hr1 : r < 1)
    (hm : (B+1)*(1+r⁻¹)/2 < C) (v : ℤ × ℤ) :
    multiCircleIntegral 1 N (fun y => canceledLatticeDensity B C S y v) =
      multiCircleIntegral r N (fun y => canceledLatticeDensity B C S y v) := by
  apply multiCircleIntegral_radius_eq N hr hr1.le
  intro y hy
  exact (canceledLatticeDensity_analyticAt hS
    (fun i => norm_pos_iff.mp (hr.trans_le (hy i).1))
    (fun i => realContourW_re_gt_one hB hr hr1 hm (hy i).1 (hy i).2) v).differentiableAt

/-- Literal double-contour-to-unit-contour attachment, every particle number
and every integer site. The subsequent angular constants remain explicit. -/
theorem unscaledLatticeCoefficient_eq_canceled_unit (N : ℕ) {lam x r : ℝ}
    (hlam : 0 < lam) (hx : 0 < x) (hr : 0 < r) (hr1 : r < 1)
    (hm : (realB lam x+1)*(1+r⁻¹)/2 < realC lam x) (v : ℤ × ℤ) :
    unscaledLatticeCoefficientAtRadius N r lam (x:ℂ) v =
      (N.factorial:ℂ)⁻¹*multiCircleIntegral 1 N
        (fun y => canceledLatticeDensity (realB lam x) (realC lam x) (spectralS (x:ℂ)) y v) := by
  have hB := (realB_pos hlam hx).le
  have hS : spectralS (x:ℂ) ≠ 0 := by
    simpa only [spectralS,← Complex.ofReal_sinh] using
      Complex.ofReal_ne_zero.mpr (Real.sinh_pos_iff.mpr hx).ne'
  rw [canceledLattice_unit_contour_eq_radius N hB hS hr hr1 hm v]
  unfold unscaledLatticeCoefficientAtRadius
  congr 1
  apply multiCircleIntegral_congr hr.le N
  intro y hy
  rw [lattice_residue_inner_integral N hr hr1 hS
    (fun i => norm_ne_zero_iff.mp ((hy i).trans_ne hr.ne'))
    (fun _ => compactLeftRoot_nonzero _)
    (fun i => realContourRoot_inside hB hr hr1 hm (hy i).ge ((hy i).le.trans hr1.le))
    (fun i => realContourRoot_physical_equation hx (y i)) v]
  exact latticeClearedNumerator_eq_canceled hB hr hr1 hm y hy v
end
end IsingBulk.Anisotropic.FormFactors
