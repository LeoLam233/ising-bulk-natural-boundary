import IsingBulk.Tail.AllBranchExteriorPositiveCoarea
import IsingBulk.Tail.CoareaRectangleKernel

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch Set MeasureTheory

def allBranchExteriorPositiveDerivative (d : LocalBranchData) (ε : ℝ) (x : ℝ × ℝ) :
    (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  ((ContinuousLinearMap.fst ℝ ℝ ℝ)+(ContinuousLinearMap.snd ℝ ℝ ℝ)).prod
    ((deriv (originalRealPhase d ε) x.1) • (ContinuousLinearMap.fst ℝ ℝ ℝ)+
      (deriv (originalRealPhase d ε) x.2) • (ContinuousLinearMap.snd ℝ ℝ ℝ))

theorem allBranchExterior_positive_hasFDerivAt {d : LocalBranchData} (B : BranchEstimates d)
    (ε a σ F₀ G₀ : ℝ) (hε : 0 < ε) (hεr : ε ≤ B.ε₀) (ha : 0 < a) (hσ : 0 < σ)
    (x : ℝ × ℝ) (hx : x ∈ allBranchExteriorPositiveRegion B.r a σ) :
    HasFDerivAt (allBranchExteriorPositivePhase d ε F₀ G₀)
      (allBranchExteriorPositiveDerivative d ε x) x := by
  have hm : x.1 ≤ B.r := by linarith [hx.2.1,hx.2.2.2]
  have hM : 0 ≤ x.2 := by linarith [hx.2.2.1]
  have h₁ := (allBranchExterior_realPhase_differentiable B ε x.1 hε hεr hx.1 hm).hasDerivAt
  have h₂ := (allBranchExterior_realPhase_differentiable B ε x.2 hε hεr hM hx.2.1).hasDerivAt
  have hf := ((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).add (hasFDerivAt_snd (𝕜 := ℝ) (p := x))).add_const F₀
  have hg := ((h₁.comp_hasFDerivAt x (hasFDerivAt_fst (𝕜 := ℝ) (p := x))).add
    (h₂.comp_hasFDerivAt x (hasFDerivAt_snd (𝕜 := ℝ) (p := x)))).add_const G₀
  convert! hf.prodMk hg using 1

theorem allBranchExterior_positive_det (d : LocalBranchData) (ε : ℝ) (x : ℝ × ℝ) :
    (allBranchExteriorPositiveDerivative d ε x).det =
      deriv (originalRealPhase d ε) x.2-deriv (originalRealPhase d ε) x.1 := by
  apply det_sum_slope_map
  intro y
  simp [allBranchExteriorPositiveDerivative]

theorem allBranchExterior_positive_jacobian_ratio {d : LocalBranchData} (B : BranchEstimates d)
    (ε a σ : ℝ) (hε : 0 < ε) (hεr : ε ≤ B.ε₀) (ha : 0 < a) (hσ : 0 < σ)
    (hsmall₁ : B.original.separationThreshold*ε ≤ a) (hsmall₂ : 2*B.original.C₀*ε ≤ a)
    (x : ℝ × ℝ) (hx : x ∈ allBranchExteriorPositiveRegion B.r a σ) :
    ‖deriv (originalPhase d ε) x.1*deriv (originalPhase d ε) x.2‖ ≤
      allBranchExteriorPositiveCost B a σ * |(allBranchExteriorPositiveDerivative d ε x).det| := by
  obtain ⟨hp,hb⟩ := allBranchExterior_positive_slope_ratio B ε a σ x.1 x.2 hε hεr ha hσ
    hsmall₁ hsmall₂ hx.1 hx.2.1 hx.2.2.1 hx.2.2.2
  rw [allBranchExterior_positive_det,abs_sub_comm,abs_of_pos hp]
  exact (div_le_iff₀ hp).mp hb

theorem allBranchExterior_positive_region_measurable (r a σ : ℝ) :
    MeasurableSet (allBranchExteriorPositiveRegion r a σ) := by
  have h : IsClosed (allBranchExteriorPositiveRegion r a σ) := by
    exact (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_snd continuous_const).inter
        ((isClosed_le continuous_const continuous_snd).inter
          (isClosed_le continuous_const (continuous_snd.sub continuous_fst))))
  exact h.measurableSet

theorem allBranchExterior_positive_coarea {d : LocalBranchData} (B : BranchEstimates d)
    (ε a σ F₀ G₀ : ℝ) (hε : 0 < ε) (hεr : ε ≤ B.ε₀) (ha : 0 < a) (hσ : 0 < σ)
    (hsmall₁ : B.original.separationThreshold*ε ≤ a) (hsmall₂ : 2*B.original.C₀*ε ≤ a)
    (k : (ℝ × ℝ) → ℝ) (hk : Continuous k) (hk0 : ∀ x, 0 ≤ k x) :
    MeasureTheory.IntegrableOn (fun x =>
      ‖deriv (originalPhase d ε) x.1*deriv (originalPhase d ε) x.2‖ *
        k (allBranchExteriorPositivePhase d ε F₀ G₀ x))
      (allBranchExteriorPositiveRegion B.r a σ) ∧
    (∫ x in allBranchExteriorPositiveRegion B.r a σ,
      ‖deriv (originalPhase d ε) x.1*deriv (originalPhase d ε) x.2‖ *
        k (allBranchExteriorPositivePhase d ε F₀ G₀ x)) ≤
      allBranchExteriorPositiveCost B a σ *
        (∫ y in Icc (F₀,G₀) (F₀+2*B.r,G₀+Real.pi), k y) := by
  have hc : ContinuousOn (fun x : ℝ × ℝ =>
      ‖deriv (originalPhase d ε) x.1*deriv (originalPhase d ε) x.2‖)
      (allBranchExteriorPositiveRegion B.r a σ) := by
    intro x hx
    have hm : x.1 ≤ B.r := by linarith [hx.2.1,hx.2.2.2]
    have hM : 0 ≤ x.2 := by linarith [hx.2.2.1]
    obtain ⟨hr₁,hi₁⟩ := B.quadrant ε x.1 hε hεr (by simpa [abs_of_nonneg hx.1] using hm)
    obtain ⟨hr₂,hi₂⟩ := B.quadrant ε x.2 hε hεr (by simpa [abs_of_nonneg hM] using hx.2.1)
    have h₁ := (currentPhase_second_hasDerivAt d ε 0 x.1 hr₁ hi₁).continuousAt
    have h₂ := (currentPhase_second_hasDerivAt d ε 0 x.2 hr₂ hi₂).continuousAt
    exact ((h₁.comp continuous_fst.continuousAt).mul
      (h₂.comp continuous_snd.continuousAt)).norm.continuousWithinAt
  have hC : 0 ≤ allBranchExteriorPositiveCost B a σ := by
    have := B.original.C_pos
    have := B.original.k_pos
    have := B.original.a_pos
    unfold allBranchExteriorPositiveCost
    positivity
  exact injective_weighted_coarea_le
    (allBranchExterior_positive_region_measurable B.r a σ)
    (allBranchExteriorPositivePhase d ε F₀ G₀) (allBranchExteriorPositiveDerivative d ε)
    (fun x hx => (allBranchExterior_positive_hasFDerivAt B ε a σ F₀ G₀ hε hεr ha hσ x hx).hasFDerivWithinAt)
    (allBranchExterior_positive_phase_injective B ε a σ F₀ G₀ hε hεr ha hσ hsmall₁ hsmall₂)
    (allBranchExterior_positive_phase_image B ε a σ F₀ G₀ hε hεr ha hσ)
    _ k hc hk hk0 (hk.continuousOn.integrableOn_compact isCompact_Icc) hC
    (fun _ _ => norm_nonneg _)
    (fun x hx => allBranchExterior_positive_jacobian_ratio B ε a σ hε hεr ha hσ hsmall₁ hsmall₂ x hx)

theorem allBranchExterior_positive_two_kernel {d : LocalBranchData} (B : BranchEstimates d)
    (ε a σ F₀ G₀ α β : ℝ) (hε : 0 < ε) (hεr : ε ≤ B.ε₀) (ha : 0 < a) (hσ : 0 < σ)
    (hsmall₁ : B.original.separationThreshold*ε ≤ a) (hsmall₂ : 2*B.original.C₀*ε ≤ a)
    (hα : 0 < α) (hα1 : α ≤ 1) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (n : ℕ) (hn : 2*B.r ≤ (n:ℝ)*(2*Real.pi)) :
    (∫ x in allBranchExteriorPositiveRegion B.r a σ,
      ‖deriv (originalPhase d ε) x.1*deriv (originalPhase d ε) x.2‖ *
        twoPhaseKernel α β (allBranchExteriorPositivePhase d ε F₀ G₀ x)) ≤
      allBranchExteriorPositiveCost B a σ *
        (((n:ℝ)*simpleKernelConstant*(1+|Real.log α|))*
          (simpleKernelConstant*(1+|Real.log β|))) := by
  have hh := (allBranchExterior_positive_coarea B ε a σ F₀ G₀ hε hεr ha hσ hsmall₁ hsmall₂
    (twoPhaseKernel α β) (twoPhaseKernel_continuous hα hβ) (twoPhaseKernel_nonneg α β)).2
  have hi := (two_simple_kernel_rectangle hα hα1 hβ hβ1 n 1
    (show F₀ ≤ F₀+2*B.r by have := B.r_pos; linarith)
    (show G₀ ≤ G₀+Real.pi by linarith [Real.pi_pos])
    (show F₀+2*B.r ≤ F₀+(n:ℝ)*(2*Real.pi) by linarith)
    (by norm_num; linarith [Real.pi_pos])).2
  have hC : 0 ≤ allBranchExteriorPositiveCost B a σ := by
    have := B.original.C_pos
    have := B.original.k_pos
    have := B.original.a_pos
    unfold allBranchExteriorPositiveCost
    positivity
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ hC
  simpa only [Nat.cast_one,one_mul,Set.Icc_prod_eq] using hi

end
end IsingBulk.Tail
