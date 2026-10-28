import IsingBulk.HT22.Tail.ShellScale

/-! The fixed-mean shell scale decays geometrically under halving the
angular diameter. The constants are independent of mean, order and epsilon. -/
namespace IsingBulk.HT22.Near
noncomputable section

theorem shellCoordinateScale_half_bounds (μ : ℝ) {r ε : ℝ}
    (hr : 0<r) (hε : 0≤ε) :
    shellCoordinateScale μ r ε/2≤shellCoordinateScale μ (r/2) ε ∧
    shellCoordinateScale μ (r/2) ε≤(Real.sqrt 2/2)*shellCoordinateScale μ r ε := by
  let T := |μ|+r+ε
  let U := |μ|+r/2+ε
  have hT : 0<T := by dsimp [T];positivity
  have hU : 0<U := by dsimp [U];positivity
  have hsT : 0<Real.sqrt T := Real.sqrt_pos.mpr hT
  have hsU : 0<Real.sqrt U := Real.sqrt_pos.mpr hU
  have hs2 : 0<Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hUT : U≤T := by dsimp [U,T];linarith
  have hTU : T≤2*U := by dsimp [T,U];nlinarith [abs_nonneg μ]
  have hsUT := Real.sqrt_le_sqrt hUT
  have hsTU := Real.sqrt_le_sqrt hTU
  rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤2)] at hsTU
  constructor
  · change (r/Real.sqrt T)/2≤(r/2)/Real.sqrt U
    have hh := div_le_div_of_nonneg_left (by positivity : 0≤r/2) hsU hsUT
    convert hh using 1; ring
  · change (r/2)/Real.sqrt U≤(Real.sqrt 2/2)*(r/Real.sqrt T)
    have hden : Real.sqrt T/Real.sqrt 2≤Real.sqrt U :=
      (div_le_iff₀ hs2).mpr (by simpa only [mul_comm] using hsTU)
    have hh := div_le_div_of_nonneg_left (by positivity : 0≤r/2)
      (div_pos hsT hs2) hden
    apply hh.trans_eq
    field_simp

theorem shellCoordinateScale_half_three_quarters (μ : ℝ) {r ε : ℝ}
    (hr : 0<r) (hε : 0≤ε) :
    shellCoordinateScale μ (r/2) ε≤(3/4:ℝ)*shellCoordinateScale μ r ε := by
  have hsq := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hs := Real.sqrt_nonneg (2:ℝ)
  have hconst : Real.sqrt 2/2≤(3/4:ℝ) := by nlinarith
  exact (shellCoordinateScale_half_bounds μ hr hε).2.trans
    (mul_le_mul_of_nonneg_right hconst (shellCoordinateScale_pos μ hr hε).le)

end
end IsingBulk.HT22.Near
