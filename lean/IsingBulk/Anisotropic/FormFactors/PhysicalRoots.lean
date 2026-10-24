import IsingBulk.Anisotropic.FormFactors.ResidueIntegral
import IsingBulk.Anisotropic.FormFactors.RealDispersion

namespace IsingBulk.Anisotropic.FormFactors
noncomputable section
open IsingBulk.Tail

theorem physical_rootEquation {lam x : ℝ} (hlam : 0 < lam) (hx : 0 < x)
    (hp : realProduct lam x ≠ 1) (q : ℝ) :
    RootEquation lam (x:ℂ) (limitingAngle q) (root (realB lam x) (realC lam x) q:ℂ) := by
  have ht : (root (realB lam x) (realC lam x) q:ℂ) +
      (root (realB lam x) (realC lam x) q:ℂ)⁻¹ =
      2*((realC lam x:ℂ)-(realB lam x:ℂ)*(Real.cos q:ℂ)) := by
    exact_mod_cast root_trace (realB_pos hlam hx).le (real_dispersion_gap hlam hx hp) q
  unfold RootEquation
  rw [ht,limitingAngle_trace]
  have hS : (Real.sinh x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sinh_pos_iff.mpr hx).ne'
  simp only [spectralA,spectralS,spectralT,realB,realC,
    ← Complex.ofReal_mul,← Complex.ofReal_cosh,← Complex.ofReal_sinh,Complex.ofReal_div]
  field_simp

/-- Every real-angle physical root is nonzero and lies strictly inside the
unit disk, on either positive real temperature side. -/
theorem physical_root_bounds {lam x : ℝ} (hlam : 0 < lam) (hx : 0 < x)
    (hp : realProduct lam x ≠ 1) (q : ℝ) :
    (root (realB lam x) (realC lam x) q:ℂ) ≠ 0 ∧
      ‖(root (realB lam x) (realC lam x) q:ℂ)‖ < 1 := by
  have h := root_bounds (realB_pos hlam hx).le (real_dispersion_gap hlam hx hp) q
  exact ⟨Complex.ofReal_ne_zero.mpr h.1.ne',by simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos h.1] using h.2⟩
end
end IsingBulk.Anisotropic.FormFactors
