import IsingBulk.Analysis.BranchSlope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Uniform integrability of the actual original branch derivative. -/
namespace IsingBulk.Branch
noncomputable section
open scoped Topology
open MeasureTheory Set

theorem reciprocal_sqrt_integral (ε r C : ℝ) (hε : 0 < ε) (hr : 0 ≤ r) (hC : 0 ≤ C) :
    (∫ u in -r..r, C/Real.sqrt (|u|+ε)) ≤ 4*C*Real.sqrt r := by
  let f := fun u : ℝ => C/Real.sqrt (|u|+ε)
  have hfc : Continuous f := continuous_const.div (continuous_abs.add continuous_const).sqrt
    (fun u => (Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (abs_nonneg u) hε)).ne')
  have hp : (∫ u in 0..r, f u) = 2*C*(Real.sqrt (r+ε)-Real.sqrt ε) := by
    have hi : IntervalIntegrable (fun u : ℝ => C/Real.sqrt (u+ε)) volume 0 r := by
      apply ContinuousOn.intervalIntegrable
      intro u hu
      have hu' : 0 ≤ u := (uIcc_of_le hr ▸ hu).1
      apply ContinuousAt.continuousWithinAt
      fun_prop (disch := positivity)
    have hd : ∀ u ∈ uIcc (0:ℝ) r,
        HasDerivAt (fun v : ℝ => 2*C*Real.sqrt (v+ε)) (C/Real.sqrt (u+ε)) u := by
      intro u hu
      have hu' : 0 ≤ u := (uIcc_of_le hr ▸ hu).1
      have h := (((hasDerivAt_id u).add_const ε).sqrt (by positivity)).const_mul (2*C)
      convert h using 1
      · rfl
      · dsimp; ring
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
    have hf : (∫ u in 0..r, f u) = ∫ u in 0..r, C/Real.sqrt (u+ε) := by
      apply intervalIntegral.integral_congr
      intro u hu
      have hu' : 0 ≤ u := (uIcc_of_le hr ▸ hu).1
      simp [f,abs_of_nonneg hu']
    rw [hf,he]
    simp
    ring
  have hn : (∫ u in -r..0, f u) = ∫ u in 0..r, f u := by
    simpa [f,abs_neg] using (intervalIntegral.integral_comp_neg (f := f) (a := 0) (b := r)).symm
  have hs : (∫ u in -r..0, f u)+(∫ u in 0..r, f u) = ∫ u in -r..r, f u :=
    intervalIntegral.integral_add_adjacent_intervals
    (hfc.intervalIntegrable (-r) 0) (hfc.intervalIntegrable 0 r)
  change (∫ u in -r..r, f u) ≤ _
  rw [← hs,hn,hp]
  have hsqrt : Real.sqrt (r+ε) ≤ Real.sqrt r+Real.sqrt ε := by
    have hs₁ := Real.sq_sqrt hr
    have hs₂ := Real.sq_sqrt hε.le
    have hs₃ := Real.sq_sqrt (show 0 ≤ r+ε by positivity)
    nlinarith [Real.sqrt_nonneg r,Real.sqrt_nonneg ε,Real.sqrt_nonneg (r+ε),
      mul_nonneg (Real.sqrt_nonneg r) (Real.sqrt_nonneg ε)]
  nlinarith [mul_le_mul_of_nonneg_left hsqrt hC]

theorem original_branch_length (d : LocalBranchData) :
    ∃ C r ε₀ : ℝ, 0 < C ∧ 0 < r ∧ 0 < ε₀ ∧ ∀ ε : ℝ,
      0 < ε → ε ≤ ε₀ →
      IntervalIntegrable (fun u => ‖deriv (originalPhase d ε) u‖) volume (-r) r ∧
      (∫ u in -r..r, ‖deriv (originalPhase d ε) u‖) ≤ C := by
  obtain ⟨c,C,r₁,_,hC,hr₁,hmagnitude⟩ := original_derivative_magnitude d
  obtain ⟨r₂,hr₂,hbranch⟩ := original_branch_inclusion d
  let r := min r₁ r₂/2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrr₁ : r < r₁ := by dsimp [r]; have := min_le_left r₁ r₂; linarith [lt_min hr₁ hr₂]
  have hrr₂ : r < r₂ := by dsimp [r]; have := min_le_right r₁ r₂; linarith [lt_min hr₁ hr₂]
  refine ⟨4*C*Real.sqrt r,r,r,by positivity,hr,hr,?_⟩
  intro ε hε hεr
  have hfun : originalPhase d ε = currentPhase d ε 0 := by funext u; rfl
  have hcont : ContinuousOn (fun u => ‖deriv (originalPhase d ε) u‖) (Icc (-r) r) := by
    intro u hu
    have hur : |u| ≤ r := abs_le.mpr hu
    obtain ⟨hre,him⟩ := hbranch ε u hε (hεr.trans_lt hrr₂) (hur.trans_lt hrr₂)
    rw [hfun]
    exact (currentPhase_second_hasDerivAt d ε 0 u hre him).continuousAt.norm.continuousWithinAt
  have hi : IntervalIntegrable (fun u => ‖deriv (originalPhase d ε) u‖) volume (-r) r :=
    ContinuousOn.intervalIntegrable (by simpa [uIcc_of_le (by linarith : -r ≤ r)] using hcont)
  refine ⟨hi,?_⟩
  have hkernel : Continuous (fun u : ℝ => C/Real.sqrt (|u|+ε)) :=
    continuous_const.div (continuous_abs.add continuous_const).sqrt
      (fun u => (Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (abs_nonneg u) hε)).ne')
  apply le_trans (intervalIntegral.integral_mono_on (by linarith) hi (hkernel.intervalIntegrable (-r) r) ?_)
    (reciprocal_sqrt_integral ε r C hε hr.le hC.le)
  intro u hu
  have hur : |u| ≤ r := abs_le.mpr hu
  exact (hmagnitude ε u hε (hεr.trans_lt hrr₁) (hur.trans_lt hrr₁)).2

end
end IsingBulk.Branch
