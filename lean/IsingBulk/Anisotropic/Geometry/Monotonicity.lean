import IsingBulk.Anisotropic.Geometry.Definitions
import Mathlib.Tactic

namespace IsingBulk.Anisotropic
noncomputable section

@[simp] theorem sliceP_zero (lam : ℝ) : sliceP lam 0 = 0 := by
  simp [sliceP]
@[simp] theorem sliceQ_zero (lam : ℝ) : sliceQ lam 0 = 0 := by
  simp [sliceQ]
@[simp] theorem sliceP_neg (lam x : ℝ) : sliceP lam (-x) = -sliceP lam x := by
  simp [sliceP, Real.cosh_neg, Real.tanh_neg]
@[simp] theorem sliceQ_neg (lam x : ℝ) : sliceQ lam (-x) = -sliceQ lam x := by
  simp [sliceQ, Real.cosh_neg, Real.tanh_neg]

theorem tanh_hasDerivAt (x : ℝ) : HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) (ne_of_gt (Real.cosh_pos x))
  convert h using 1
  · ext y
    exact Real.tanh_eq_sinh_div_cosh y
  · congr 1
    nlinarith [Real.cosh_sq_sub_sinh_sq x]

theorem tanh_strictMono : StrictMono Real.tanh := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(tanh_hasDerivAt x).deriv]
  positivity

theorem tanh_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.tanh x := by
  simpa only [Real.tanh_zero] using tanh_strictMono.monotone hx

theorem sliceP_hasDerivAt (lam x : ℝ) : HasDerivAt (sliceP lam)
    (Real.sinh x * Real.tanh (lam*x) + Real.cosh x * (lam / Real.cosh (lam*x)^2)) x := by
  have h := (Real.hasDerivAt_cosh x).mul ((tanh_hasDerivAt (lam*x)).comp x
    ((hasDerivAt_id x).const_mul lam))
  convert h using 1
  · rfl
  · dsimp
    ring

theorem sliceP_strictMono {lam : ℝ} (hlam : 0 < lam) : StrictMono (sliceP lam) := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(sliceP_hasDerivAt lam x).deriv]
  have ht : 0 ≤ Real.sinh x * Real.tanh (lam*x) := by
    rcases le_total 0 x with hx | hx
    · exact mul_nonneg (Real.sinh_nonneg_iff.mpr hx) (tanh_nonneg (mul_nonneg hlam.le hx))
    · have h1 : Real.sinh x ≤ 0 := Real.sinh_nonpos_iff.mpr hx
      have h2 : Real.tanh (lam*x) ≤ 0 := by
        simpa only [Real.tanh_zero] using tanh_strictMono.monotone (mul_nonpos_of_nonneg_of_nonpos hlam.le hx)
      exact mul_nonneg_of_nonpos_of_nonpos h1 h2
  have hp : 0 < Real.cosh x * (lam / Real.cosh (lam*x)^2) := by positivity
  linarith

theorem sliceQ_eq_swapped (lam x : ℝ) (hlam : lam ≠ 0) :
    sliceQ lam x = sliceP lam⁻¹ (lam*x) := by
  simp [sliceP, sliceQ, inv_mul_cancel_left₀ hlam]

theorem sliceQ_strictMono {lam : ℝ} (hlam : 0 < lam) : StrictMono (sliceQ lam) := by
  intro x y hxy
  rw [sliceQ_eq_swapped lam x (ne_of_gt hlam), sliceQ_eq_swapped lam y (ne_of_gt hlam)]
  exact sliceP_strictMono (inv_pos.mpr hlam) (mul_lt_mul_of_pos_left hxy hlam)

@[simp] theorem sliceP_isotropic (x : ℝ) : sliceP 1 x = Real.sinh x := by
  simp only [sliceP, one_mul, Real.tanh_eq_sinh_div_cosh]
  field_simp

@[simp] theorem sliceQ_isotropic (x : ℝ) : sliceQ 1 x = Real.sinh x := by
  simp only [sliceQ, one_mul, Real.tanh_eq_sinh_div_cosh]
  field_simp

end
end IsingBulk.Anisotropic
