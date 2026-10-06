import IsingBulk.Tail.ClosedUpperRoot
import IsingBulk.Tail.CompactRootGroups
import Mathlib.Topology.UniformSpace.HeineCantor

/-! Continuous boundary values at the branch point as well as the regular
real intervals. No holomorphic extension through the branch is asserted. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Filter Set
open scoped Topology

theorem continuedRoot_continuousAt_one : ContinuousAt continuedRoot (1:ℂ) := by
  have hl : ContinuousAt compactLeftRoot (1:ℂ) := by
    unfold compactLeftRoot
    apply continuousAt_id.sub
    apply ContinuousAt.mul
    · exact (Complex.continuousAt_sqrt (Or.inl (by norm_num))).comp
        (continuousAt_id.sub continuousAt_const)
    · exact (Complex.continuousAt_sqrt (Or.inl (by norm_num))).comp
        (continuousAt_id.add continuousAt_const)
  have hr : ContinuousAt interiorRoot (1:ℂ) := by
    unfold interiorRoot inverseCosineRoot
    apply ContinuousAt.inv₀
    · apply continuousAt_id.add
      apply continuousAt_const.mul
      exact (Complex.continuousAt_sqrt (Or.inl (by norm_num))).comp
        (continuousAt_const.sub (continuousAt_id.pow 2))
    · norm_num
  have hle : compactLeftRoot (1:ℂ)=1 := by simp [compactLeftRoot]
  have hre : interiorRoot (1:ℂ)=1 := by simp [interiorRoot,inverseCosineRoot]
  have he : continuedRoot (1:ℂ)=1 := by simp [continuedRoot,hre]
  change Tendsto continuedRoot (𝓝 (1:ℂ)) (𝓝 (continuedRoot 1))
  rw [he]
  unfold continuedRoot
  have hl' : Tendsto compactLeftRoot (𝓝 (1:ℂ)) (𝓝 (1:ℂ)) := by simpa only [hle] using hl.tendsto
  have hr' : Tendsto interiorRoot (𝓝 (1:ℂ)) (𝓝 (1:ℂ)) := by simpa only [hre] using hr.tendsto
  exact hl'.if' hr' 

theorem continuedRoot_continuousAt_real {w : ℝ} (hw : -1 < w) :
    ContinuousAt continuedRoot (w:ℂ) := by
  by_cases he : w=1
  · simpa [he] using continuedRoot_continuousAt_one
  · apply (continuedRoot_analyticAt _).continuousAt
    by_cases hl : 1 < w
    · exact Or.inl (Or.inr (by simpa using hl))
    · exact Or.inr (by change |w| < 1; rw [abs_lt]; exact ⟨hw,lt_of_le_of_ne (le_of_not_gt hl) he⟩)

theorem continuedRoot_eq_closedUpper_of_continuous {W : ℂ} (hi : 0 ≤ W.im)
    (hc : ContinuousAt continuedRoot W) : continuedRoot W=closedUpperRoot W := by
  have hp : Continuous (fun t : ℝ => W+(t:ℂ)*Complex.I) := by fun_prop
  have ht : Tendsto (fun t : ℝ => W+(t:ℂ)*Complex.I) (𝓝[>] 0) (𝓝 W) := by
    simpa using (hp.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  have he : (fun t : ℝ => continuedRoot (W+(t:ℂ)*Complex.I)) =ᶠ[𝓝[>] 0]
      (fun t : ℝ => closedUpperRoot (W+(t:ℂ)*Complex.I)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hu : 0 < (W+(t:ℂ)*Complex.I).im := by simp only [Complex.add_im,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero]; exact add_pos_of_nonneg_of_pos hi ht
    rw [continuedRoot_eq_interiorRoot hu,closedUpperRoot_eq_physical hu]
  exact tendsto_nhds_unique (hc.tendsto.comp ht)
    ((closedUpperRoot_continuous.continuousAt.tendsto.comp ht).congr' he.symm)

theorem continuedRoot_eq_closedUpper_real {w : ℝ} (hw : -1 < w) :
    continuedRoot (w:ℂ)=closedUpperRoot (w:ℂ) :=
  continuedRoot_eq_closedUpper_of_continuous (by simp) (continuedRoot_continuousAt_real hw)

theorem continuedRoot_real_lower_bounds {w : ℝ} (hw : -1 < w) :
    ‖continuedRoot (w:ℂ)‖ ≤ 1 ∧ (continuedRoot (w:ℂ)).im ≤ 0 := by
  by_cases he : w=1
  · simp [he,continuedRoot,interiorRoot,inverseCosineRoot]
  · apply continuedRoot_closed_upper_bounds _ (by simp)
    by_cases hl : 1 < w
    · exact Or.inl (Or.inr (by simpa using hl))
    · exact Or.inr (by change |w|<1; exact abs_lt.mpr ⟨hw,lt_of_le_of_ne (le_of_not_gt hl) he⟩)

theorem continuedRoot_real_ne_one {w : ℝ} (hw : w ≠ 1) :
    continuedRoot (w:ℂ) ≠ 1 := by
  intro hz
  have h := continuedRoot_quadratic (w:ℂ)
  rw [hz] at h
  have he : (w:ℂ)=1 := by linear_combination -h/2
  exact hw (by exact_mod_cast he)

theorem continuedRoot_real_ne_neg_one {w : ℝ} (hw : -1 < w) :
    continuedRoot (w:ℂ) ≠ -1 := by
  intro hz
  have h := continuedRoot_quadratic (w:ℂ)
  rw [hz] at h
  have he : (w:ℂ)= -1 := by linear_combination h/2
  have he' : w= -1 := by exact_mod_cast he
  linarith

end
end IsingBulk.Tail
