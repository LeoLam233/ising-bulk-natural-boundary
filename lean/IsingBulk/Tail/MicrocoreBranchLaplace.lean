import IsingBulk.Tail.MicrocorePhaseMagnitude
import IsingBulk.Tail.MicrocoreLaplaceKernel
import IsingBulk.Analysis.BranchLength

/-! Laplace transform of the actual branch arclength measure. Both sides
of the original lower branch are included; all constants precede ε,b,t. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch MeasureTheory Set

def branchCurveLaplace (d : LocalBranchData) (ε t u : ℝ) : ℝ :=
  Real.exp (-t*‖originalPhase d ε u‖)*‖deriv (originalPhase d ε) u‖

 theorem original_branch_laplace_bound (d : LocalBranchData) :
    ∃ K r : ℝ, 0 < K ∧ 0 < r ∧ ∀ ε b t : ℝ,
      0 < ε → ε < r → 0 < b → b < r → 0 < t →
      IntervalIntegrable (branchCurveLaplace d ε t) volume (-b) b ∧
      (∫ u in -b..b, branchCurveLaplace d ε t u) ≤ K*min (Real.sqrt b) t⁻¹ := by
  obtain ⟨c,C,rφ,hc,_,hrφ,hφ⟩ := original_phase_magnitude d
  obtain ⟨cd,Cd,rd,_,hCd,hrd,hderiv⟩ := original_derivative_magnitude d
  obtain ⟨rb,hrb,hbranch⟩ := original_branch_inclusion d
  let r := min rφ (min rd rb)/2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrs : r < rφ ∧ r < rd ∧ r < rb := by
    have hh : r < min rφ (min rd rb) := half_lt_self (lt_min hrφ (lt_min hrd hrb))
    simpa only [lt_min_iff] using hh
  let K := 4*Cd+4*Cd/c
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K,r,hK,hr,?_⟩
  intro ε b t hε hεr hb hbr ht
  have hcont : ContinuousOn (branchCurveLaplace d ε t) (Icc (-b) b) := by
    intro u hu
    have hur : |u| < r := (abs_le.mpr hu).trans_lt hbr
    obtain ⟨hre,him⟩ := hbranch ε u hε (hεr.trans hrs.2.2) (hur.trans hrs.2.2)
    have hp := (currentPhase_hasDerivAt d ε 0 u hre him).continuousAt
    have hd := (currentPhase_second_hasDerivAt d ε 0 u hre him).continuousAt
    have hx : ContinuousAt (fun q => Real.exp (-t*‖currentPhase d ε 0 q‖)*
        ‖deriv (currentPhase d ε 0) q‖) u :=
      (Real.continuous_exp.continuousAt.comp (hp.norm.const_mul (-t))).mul hd.norm
    exact hx.continuousWithinAt
  have hint : IntervalIntegrable (branchCurveLaplace d ε t) volume (-b) b :=
    ContinuousOn.intervalIntegrable (by simpa [uIcc_of_le (by linarith : -b ≤ b)] using hcont)
  have hker : Continuous (fun u : ℝ => Cd/Real.sqrt (|u|+ε)) :=
    continuous_const.div (continuous_abs.add continuous_const).sqrt
      (fun u => (Real.sqrt_pos.mpr (by positivity : 0 < |u|+ε)).ne')
  have hpoint : ∀ u ∈ Icc (-b) b, branchCurveLaplace d ε t u ≤ Cd/Real.sqrt (|u|+ε) := by
    intro u hu
    have hur : |u| < r := (abs_le.mpr hu).trans_lt hbr
    have hd := (hderiv ε u hε (hεr.trans hrs.2.1) (hur.trans hrs.2.1)).2
    have he : Real.exp (-t*‖originalPhase d ε u‖) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [norm_nonneg (originalPhase d ε u)])
    exact (mul_le_of_le_one_left (norm_nonneg _) he).trans hd
  have hL : (∫ u in -b..b, branchCurveLaplace d ε t u) ≤ 4*Cd*Real.sqrt b :=
    (intervalIntegral.integral_mono_on (by linarith) hint (hker.intervalIntegrable _ _) hpoint).trans
      (reciprocal_sqrt_integral ε b Cd hε hb.le hCd.le)
  have hmodel : Continuous (fun u => Cd*sqrtLaplaceKernel (t*c) ε u) :=
    continuous_const.mul (sqrtLaplaceKernel_continuous _ _ hε)
  have hpoint' : ∀ u ∈ Icc (-b) b,
      branchCurveLaplace d ε t u ≤ Cd*sqrtLaplaceKernel (t*c) ε u := by
    intro u hu
    have hur : |u| < r := (abs_le.mpr hu).trans_lt hbr
    have hl := (hφ ε u hε (hεr.trans hrs.1) (hur.trans hrs.1)).1
    have hd := (hderiv ε u hε (hεr.trans hrs.2.1) (hur.trans hrs.2.1)).2
    have he : Real.exp (-t*‖originalPhase d ε u‖) ≤ Real.exp (-(t*c)*Real.sqrt (|u|+ε)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hh := mul_le_mul he hd (norm_nonneg _) (Real.exp_pos _).le
    unfold branchCurveLaplace sqrtLaplaceKernel
    convert hh using 1
    ring
  have hT : (∫ u in -b..b, branchCurveLaplace d ε t u) ≤ Cd*(4/(t*c)) := by
    apply (intervalIntegral.integral_mono_on (by linarith) hint (hmodel.intervalIntegrable _ _) hpoint').trans
    rw [intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left (sqrt_laplace_integral (t*c) ε b (mul_pos ht hc) hε hb.le) hCd.le
  refine ⟨hint,?_⟩
  rw [mul_min_of_nonneg _ _ hK.le]
  apply le_min
  · apply hL.trans
    have hk : 4*Cd ≤ K := by
      dsimp [K]
      have hh : 0 ≤ 4*Cd/c := by positivity
      linarith
    exact mul_le_mul_of_nonneg_right hk (Real.sqrt_nonneg b)
  · apply hT.trans
    have he : Cd*(4/(t*c))=(4*Cd/c)*t⁻¹ := by ring
    rw [he]
    have hk : 4*Cd/c ≤ K := by dsimp [K]; linarith
    exact mul_le_mul_of_nonneg_right hk (inv_nonneg.mpr ht.le)

end
end IsingBulk.Tail
