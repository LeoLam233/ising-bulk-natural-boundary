import IsingBulk.Anisotropic.Geometry.AnalyticProfiles

namespace IsingBulk.Anisotropic
noncomputable section

/-- The scaled hyperbolic cotangent controlling the anisotropic opening. -/
def openingScaledCoth (t : ℝ) : ℝ := t*Real.cosh t/Real.sinh t

theorem openingScaledCoth_hasDerivAt {t : ℝ} (ht : 0<t) :
    HasDerivAt openingScaledCoth
      ((Real.sinh t*Real.cosh t-t)/Real.sinh t^2) t := by
  have hn : Real.sinh t≠0 := (Real.sinh_pos_iff.mpr ht).ne'
  have h := ((hasDerivAt_id t).mul (Real.hasDerivAt_cosh t)).div
    (Real.hasDerivAt_sinh t) hn
  have he : (1*Real.cosh t+t*Real.sinh t)*Real.sinh t-
      t*Real.cosh t*Real.cosh t=Real.sinh t*Real.cosh t-t := by
    linear_combination -t*(Real.cosh_sq_sub_sinh_sq t)
  change HasDerivAt openingScaledCoth
    (((1*Real.cosh t+t*Real.sinh t)*Real.sinh t-
      t*Real.cosh t*Real.cosh t)/Real.sinh t^2) t at h
  rwa [he] at h

theorem openingScaledCoth_deriv_pos {t : ℝ} (ht : 0<t) :
    0<deriv openingScaledCoth t := by
  rw [(openingScaledCoth_hasDerivAt ht).deriv]
  have hh := Real.self_lt_sinh_iff.mpr (show 0<2*t by positivity)
  rw [Real.sinh_two_mul] at hh
  apply div_pos _ (sq_pos_of_pos (Real.sinh_pos_iff.mpr ht))
  linarith

theorem openingScaledCoth_strictMonoOn : StrictMonoOn openingScaledCoth (Set.Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro t ht
    exact (openingScaledCoth_hasDerivAt ht).continuousAt.continuousWithinAt
  · intro t ht
    exact openingScaledCoth_deriv_pos (by simpa only [interior_Ioi,Set.mem_Ioi] using ht)

/-- The displayed width coefficient is strictly positive for every strict
positive anisotropy, using the actual critical point. -/
theorem anisotropic_opening_coefficient_pos {lam : ℝ} (hlam : 0<lam) (hne : lam≠1) :
    0<(1/2:ℝ)*|lam*(Real.cosh (lam*criticalPoint lam)/Real.sinh (lam*criticalPoint lam))-
      Real.cosh (criticalPoint lam)/Real.sinh (criticalPoint lam)| := by
  have hx := criticalPoint_pos hlam
  have hlx := mul_pos hlam hx
  have harg : lam*criticalPoint lam≠criticalPoint lam := by
    intro h
    apply hne
    nlinarith
  have hneq := openingScaledCoth_strictMonoOn.injOn.ne hlx hx harg
  have hc : lam*(Real.cosh (lam*criticalPoint lam)/Real.sinh (lam*criticalPoint lam))-
      Real.cosh (criticalPoint lam)/Real.sinh (criticalPoint lam)≠0 := by
    intro h
    apply hneq
    unfold openingScaledCoth
    have hh := congrArg (fun a : ℝ=>criticalPoint lam*a) (sub_eq_zero.mp h)
    convert hh using 1 <;> ring
  exact mul_pos (by norm_num) (abs_pos.mpr hc)

end
end IsingBulk.Anisotropic
