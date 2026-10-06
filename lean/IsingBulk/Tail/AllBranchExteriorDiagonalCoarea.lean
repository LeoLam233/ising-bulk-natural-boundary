import IsingBulk.Tail.AllBranchExteriorPositiveJacobian

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch Set MeasureTheory

def allBranchExteriorPositiveOpenPair (r a : ℝ) : Set (ℝ × ℝ) :=
  {x | 0 ≤ x.1 ∧ x.2 ≤ r ∧ a ≤ x.2 ∧ x.1 < x.2}

def allBranchExteriorDiagonalCost {d : LocalBranchData} (B : BranchEstimates d) (a : ℝ) : ℝ :=
  (B.original.C^2/min (B.original.k/4) (B.original.a/2))*B.r/Real.sqrt a+
    (2*B.original.C^2/B.original.k)*Real.sqrt B.r

theorem allBranchExterior_open_pair_mem {r a : ℝ} {x : ℝ × ℝ}
    (hx : x ∈ allBranchExteriorPositiveOpenPair r a) :
    x ∈ allBranchExteriorPositiveRegion r a (x.2-x.1) :=
  ⟨hx.1,hx.2.1,hx.2.2.1,le_rfl⟩

theorem allBranchExterior_diagonal_jacobian_ratio {d : LocalBranchData} (B : BranchEstimates d)
    (ε a : ℝ) (hε : 0 < ε) (hεr : ε ≤ B.ε₀) (ha : 0 < a)
    (hsmall₁ : B.original.separationThreshold*ε ≤ a) (hsmall₂ : 2*B.original.C₀*ε ≤ a)
    (x : ℝ × ℝ) (hx : x ∈ allBranchExteriorPositiveOpenPair B.r a) :
    (x.2-x.1)*‖deriv (originalPhase d ε) x.1*deriv (originalPhase d ε) x.2‖ ≤
      allBranchExteriorDiagonalCost B a*|(allBranchExteriorPositiveDerivative d ε x).det| := by
  have hd : 0 < x.2-x.1 := sub_pos.mpr hx.2.2.2
  have hh := allBranchExterior_positive_jacobian_ratio B ε a (x.2-x.1) hε hεr ha hd
    hsmall₁ hsmall₂ x (allBranchExterior_open_pair_mem hx)
  have hb := mul_le_mul_of_nonneg_left hh hd.le
  have hcost : (x.2-x.1)*allBranchExteriorPositiveCost B a (x.2-x.1) ≤
      allBranchExteriorDiagonalCost B a := by
    have he : (x.2-x.1)*allBranchExteriorPositiveCost B a (x.2-x.1)=
        (B.original.C^2/min (B.original.k/4) (B.original.a/2))*(x.2-x.1)/Real.sqrt a+
          (2*B.original.C^2/B.original.k)*Real.sqrt B.r := by
      unfold allBranchExteriorPositiveCost
      field_simp
    rw [he]
    unfold allBranchExteriorDiagonalCost
    have hcoef : 0 ≤ B.original.C^2/min (B.original.k/4) (B.original.a/2) := by
      have := B.original.k_pos
      have := B.original.a_pos
      positivity
    gcongr
    linarith [hx.1,hx.2.1]
  exact hb.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcost (abs_nonneg _))

theorem allBranchExterior_open_pair_injective {d : LocalBranchData} (B : BranchEstimates d)
    (ε a F₀ G₀ : ℝ) (hε : 0 < ε) (hεr : ε ≤ B.ε₀) (ha : 0 < a)
    (hsmall₁ : B.original.separationThreshold*ε ≤ a) (hsmall₂ : 2*B.original.C₀*ε ≤ a) :
    InjOn (allBranchExteriorPositivePhase d ε F₀ G₀) (allBranchExteriorPositiveOpenPair B.r a) := by
  intro x hx y hy he
  let σ := min (x.2-x.1) (y.2-y.1)
  have hσ : 0 < σ := lt_min (sub_pos.mpr hx.2.2.2) (sub_pos.mpr hy.2.2.2)
  apply allBranchExterior_positive_phase_injective B ε a σ F₀ G₀ hε hεr ha hσ hsmall₁ hsmall₂ _ _ he
  · exact ⟨hx.1,hx.2.1,hx.2.2.1,min_le_left _ _⟩
  · exact ⟨hy.1,hy.2.1,hy.2.2.1,min_le_right _ _⟩

theorem allBranchExterior_diagonal_coarea {d : LocalBranchData} (B : BranchEstimates d)
    (ε a F₀ G₀ : ℝ) (hε : 0 < ε) (hεr : ε ≤ B.ε₀) (ha : 0 < a)
    (hsmall₁ : B.original.separationThreshold*ε ≤ a) (hsmall₂ : 2*B.original.C₀*ε ≤ a)
    (k : (ℝ × ℝ) → ℝ) (hk : Continuous k) (hk0 : ∀ x, 0 ≤ k x) :
    IntegrableOn (fun x => (x.2-x.1)*
      ‖deriv (originalPhase d ε) x.1*deriv (originalPhase d ε) x.2‖*
      k (allBranchExteriorPositivePhase d ε F₀ G₀ x)) (allBranchExteriorPositiveOpenPair B.r a) ∧
    (∫ x in allBranchExteriorPositiveOpenPair B.r a, (x.2-x.1)*
      ‖deriv (originalPhase d ε) x.1*deriv (originalPhase d ε) x.2‖*
      k (allBranchExteriorPositivePhase d ε F₀ G₀ x)) ≤
      allBranchExteriorDiagonalCost B a*(∫ y in Icc (F₀,G₀) (F₀+2*B.r,G₀+Real.pi), k y) := by
  have hS : MeasurableSet (allBranchExteriorPositiveOpenPair B.r a) := by
    unfold allBranchExteriorPositiveOpenPair
    measurability
  have hdiff : ∀ x ∈ allBranchExteriorPositiveOpenPair B.r a,
      HasFDerivWithinAt (allBranchExteriorPositivePhase d ε F₀ G₀)
        (allBranchExteriorPositiveDerivative d ε x) (allBranchExteriorPositiveOpenPair B.r a) x := by
    intro x hx
    exact (allBranchExterior_positive_hasFDerivAt B ε a (x.2-x.1) F₀ G₀ hε hεr ha
      (sub_pos.mpr hx.2.2.2) x (allBranchExterior_open_pair_mem hx)).hasFDerivWithinAt
  have himage : allBranchExteriorPositivePhase d ε F₀ G₀ '' allBranchExteriorPositiveOpenPair B.r a ⊆
      Icc (F₀,G₀) (F₀+2*B.r,G₀+Real.pi) := by
    rintro y ⟨x,hx,rfl⟩
    exact allBranchExterior_positive_phase_image B ε a (x.2-x.1) F₀ G₀ hε hεr ha
      (sub_pos.mpr hx.2.2.2) ⟨x,allBranchExterior_open_pair_mem hx,rfl⟩
  have hw : ContinuousOn (fun x : ℝ × ℝ => (x.2-x.1)*
      ‖deriv (originalPhase d ε) x.1*deriv (originalPhase d ε) x.2‖) (allBranchExteriorPositiveOpenPair B.r a) := by
    intro x hx
    have hm : x.1 ≤ B.r := hx.2.2.2.le.trans hx.2.1
    have hM : 0 ≤ x.2 := ha.le.trans hx.2.2.1
    obtain ⟨hr₁,hi₁⟩ := B.quadrant ε x.1 hε hεr (by simpa [abs_of_nonneg hx.1] using hm)
    obtain ⟨hr₂,hi₂⟩ := B.quadrant ε x.2 hε hεr (by simpa [abs_of_nonneg hM] using hx.2.1)
    have h₁ := (currentPhase_second_hasDerivAt d ε 0 x.1 hr₁ hi₁).continuousAt
    have h₂ := (currentPhase_second_hasDerivAt d ε 0 x.2 hr₂ hi₂).continuousAt
    exact (((continuous_snd.sub continuous_fst).continuousAt).mul
      ((h₁.comp continuous_fst.continuousAt).mul (h₂.comp continuous_snd.continuousAt)).norm).continuousWithinAt
  have hC : 0 ≤ allBranchExteriorDiagonalCost B a := by
    have := B.original.k_pos
    have := B.original.a_pos
    have := B.r_pos
    unfold allBranchExteriorDiagonalCost
    positivity
  exact injective_weighted_coarea_le hS _ _ hdiff
    (allBranchExterior_open_pair_injective B ε a F₀ G₀ hε hεr ha hsmall₁ hsmall₂)
    himage _ k hw hk hk0 (hk.continuousOn.integrableOn_compact isCompact_Icc) hC
    (fun x hx => mul_nonneg (sub_pos.mpr hx.2.2.2).le (norm_nonneg _))
    (fun x hx => allBranchExterior_diagonal_jacobian_ratio B ε a hε hεr ha hsmall₁ hsmall₂ x hx)

end
end IsingBulk.Tail
