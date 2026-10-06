import IsingBulk.Analysis.BranchSecondDerivative

namespace IsingBulk.Branch
noncomputable section
open scoped Topology

theorem realPhase_second_deriv (d : LocalBranchData) (ε t u : ℝ)
    (hre : 0 < (currentW d ε t u).re) (him : 0 < (currentW d ε t u).im) :
    deriv (deriv (fun v => (currentPhase d ε t v).re)) u =
      (deriv (deriv (currentPhase d ε t)) u).re := by
  have hd := currentPhase_second_hasDerivAt d ε t u hre him
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt u hd
  have he : deriv (fun v => (currentPhase d ε t v).re) =ᶠ[𝓝 u]
      (fun v => (deriv (currentPhase d ε t) v).re) := by
    filter_upwards [current_phase_quadrant_near d ε t u hre him] with v hv
    exact realPhase_deriv d ε t v hv.1 hv.2
  have hr' := hr.congr_of_eventuallyEq he
  simpa [Function.comp_def,hd.deriv] using hr'.deriv

theorem original_positive_slope (d : LocalBranchData) :
    ∃ c C r : ℝ, 0 < c ∧ 0 < C ∧ 0 < r ∧ ∀ ε u : ℝ,
      0 < ε → ε < r → 0 ≤ u → u < r →
      c/Real.sqrt (u+ε) ≤ deriv (originalRealPhase d ε) u ∧
      deriv (originalRealPhase d ε) u ≤ C/Real.sqrt (u+ε) := by
  obtain ⟨c,C,r₁,hc,hC,hr₁,hmagnitude⟩ := current_derivative_magnitude d
  obtain ⟨r₂,hr₂,hcone⟩ := current_positive_cone d
  obtain ⟨r₃,hr₃,hbranch⟩ := current_branch_inclusion d
  let r := min r₁ (min r₂ r₃)
  refine ⟨(2/3)*c,C,r,by positivity,hC,lt_min hr₁ (lt_min hr₂ hr₃),?_⟩
  intro ε u hε hεr hu hur
  have hr₁' : r ≤ r₁ := min_le_left _ _
  have hr₂' : r ≤ r₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hr₃' : r ≤ r₃ := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨hm,hm'⟩ := hmagnitude ε 0 u hε (hεr.trans_le hr₁') le_rfl hr₁
    (by simpa [abs_of_nonneg hu] using hur.trans_le hr₁')
  have hcon := hcone ε 0 u hε (hεr.trans_le hr₂') le_rfl hr₂ hu (hur.trans_le hr₂')
  obtain ⟨hre,him⟩ := hbranch ε 0 u hε (hεr.trans_le hr₃') le_rfl hr₃
    (by simpa [abs_of_nonneg hu] using hur.trans_le hr₃')
  have he : originalRealPhase d ε = (fun v => (currentPhase d ε 0 v).re) := by funext v; rfl
  rw [he,realPhase_deriv d ε 0 u hre him]
  simp only [abs_of_nonneg hu,add_zero] at hm hm'
  constructor
  · calc
      (2/3)*c/Real.sqrt (u+ε) = (2/3)*(c/Real.sqrt (u+ε)) := by ring
      _ ≤ (2/3)*‖deriv (currentPhase d ε 0) u‖ := mul_le_mul_of_nonneg_left hm (by norm_num)
      _ ≤ _ := hcon
  · exact (Complex.re_le_norm _).trans hm'

end
end IsingBulk.Branch
