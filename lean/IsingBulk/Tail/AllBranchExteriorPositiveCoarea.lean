import IsingBulk.Analysis.BranchEndpoint
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! The actual positive all-B extreme-pair phase map. Only the two extrema
vary; additive phases from other coordinates merely translate the image. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch Set

def allBranchExteriorPositiveRegion (r a σ : ℝ) : Set (ℝ × ℝ) :=
  {x | 0 ≤ x.1 ∧ x.2 ≤ r ∧ a ≤ x.2 ∧ σ ≤ x.2-x.1}

def allBranchExteriorPositivePhase (d : LocalBranchData) (ε F₀ G₀ : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (x.1+x.2+F₀,originalRealPhase d ε x.1+originalRealPhase d ε x.2+G₀)

def allBranchExteriorPositiveCost {d : LocalBranchData} (B : BranchEstimates d) (a σ : ℝ) : ℝ :=
  (B.original.C^2/min (B.original.k/4) (B.original.a/2))/Real.sqrt a+
    (2*B.original.C^2/B.original.k)*Real.sqrt B.r/σ

theorem allBranchExterior_positive_slope_ratio {d : LocalBranchData} (B : BranchEstimates d)
    (ε a σ m M : ℝ) (hε : 0 < ε) (hεr : ε ≤ B.ε₀) (ha : 0 < a) (hσ : 0 < σ)
    (hsmall₁ : B.original.separationThreshold*ε ≤ a) (hsmall₂ : 2*B.original.C₀*ε ≤ a)
    (hm : 0 ≤ m) (hMr : M ≤ B.r) (haM : a ≤ M) (hgap : σ ≤ M-m) :
    0 < deriv (originalRealPhase d ε) m-deriv (originalRealPhase d ε) M ∧
      ‖deriv (originalPhase d ε) m*deriv (originalPhase d ε) M‖/
        (deriv (originalRealPhase d ε) m-deriv (originalRealPhase d ε) M) ≤
        allBranchExteriorPositiveCost B a σ := by
  have hmM : m < M := by linarith
  have hM : 0 < M := ha.trans_le haM
  have hC₁ : 0 < B.original.C^2/min (B.original.k/4) (B.original.a/2) := by
    have hk := B.original.k_pos
    have ha := B.original.a_pos
    have hc := B.original.C_pos
    positivity
  have hC₂ : 0 < 2*B.original.C^2/B.original.k := by
    have hk := B.original.k_pos
    have hc := B.original.C_pos
    positivity
  by_cases hsep : m ≤ M/2
  · obtain ⟨_,hpos,hbound⟩ := B.separated ε m M hε hεr hm hsep hMr (hsmall₁.trans haM)
    refine ⟨hpos,?_⟩
    apply hbound.trans
    have hh := div_le_div_of_nonneg_left hC₁.le (Real.sqrt_pos.mpr ha) (Real.sqrt_le_sqrt haM)
    have hp : 0 ≤ (2*B.original.C^2/B.original.k)*Real.sqrt B.r/σ := by positivity
    unfold allBranchExteriorPositiveCost
    linarith
  · have hm' : M/2 < m := lt_of_not_ge hsep
    have hscale : B.original.C₀*ε ≤ m := by linarith
    obtain ⟨hpos,hbound⟩ := B.comparable ε m M hε hεr hscale hm' hmM hMr
    refine ⟨hpos,?_⟩
    apply hbound.trans
    have hh : (2*B.original.C^2/B.original.k)*Real.sqrt M/(M-m) ≤
        (2*B.original.C^2/B.original.k)*Real.sqrt B.r/σ :=
      div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hMr) hC₂.le) hσ hgap
    have hp : 0 ≤ (B.original.C^2/min (B.original.k/4) (B.original.a/2))/Real.sqrt a := by positivity
    unfold allBranchExteriorPositiveCost
    linarith

theorem allBranchExterior_realPhase_differentiable {d : LocalBranchData} (B : BranchEstimates d)
    (ε u : ℝ) (hε : 0 < ε) (hεr : ε ≤ B.ε₀) (hu : 0 ≤ u) (hur : u ≤ B.r) :
    DifferentiableAt ℝ (originalRealPhase d ε) u := by
  obtain ⟨hre,him⟩ := B.quadrant ε u hε hεr (by simpa [abs_of_nonneg hu] using hur)
  have hh := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt u
    (currentPhase_hasDerivAt d ε 0 u hre him)).differentiableAt
  convert! hh using 1

theorem allBranchExterior_positive_phase_injective {d : LocalBranchData} (B : BranchEstimates d)
    (ε a σ F₀ G₀ : ℝ) (hε : 0 < ε) (hεr : ε ≤ B.ε₀) (ha : 0 < a) (hσ : 0 < σ)
    (hsmall₁ : B.original.separationThreshold*ε ≤ a) (hsmall₂ : 2*B.original.C₀*ε ≤ a) :
    InjOn (allBranchExteriorPositivePhase d ε F₀ G₀) (allBranchExteriorPositiveRegion B.r a σ) := by
  have hord : ∀ m₁ M₁ m₂ M₂ : ℝ,
      (m₁,M₁) ∈ allBranchExteriorPositiveRegion B.r a σ →
      (m₂,M₂) ∈ allBranchExteriorPositiveRegion B.r a σ → m₁ < m₂ →
      m₁+M₁=m₂+M₂ →
      originalRealPhase d ε m₁+originalRealPhase d ε M₁ <
        originalRealPhase d ε m₂+originalRealPhase d ε M₂ := by
    intro m₁ M₁ m₂ M₂ h₁ h₂ hm hF
    let S := m₁+M₁
    let g : ℝ → ℝ := fun t => originalRealPhase d ε t+originalRealPhase d ε (S-t)
    have hcell : ∀ t ∈ Icc m₁ m₂, (t,S-t) ∈ allBranchExteriorPositiveRegion B.r a σ := by
      intro t ht
      dsimp [allBranchExteriorPositiveRegion] at h₁ h₂ ⊢
      dsimp [S]
      constructor
      · linarith [ht.1]
      · constructor
        · linarith [ht.1]
        · constructor <;> linarith [ht.2]
    have hdiff : ∀ t ∈ Icc m₁ m₂,
        HasDerivAt g (deriv (originalRealPhase d ε) t-deriv (originalRealPhase d ε) (S-t)) t := by
      intro t ht
      have hh := hcell t ht
      have htR : t ≤ B.r := by linarith [hh.2.1,hh.2.2.2]
      have hSpos : 0 ≤ S-t := by linarith [hh.2.2.1]
      have hd₁ := (allBranchExterior_realPhase_differentiable B ε t hε hεr hh.1 htR).hasDerivAt
      have hd₂ := (allBranchExterior_realPhase_differentiable B ε (S-t) hε hεr hSpos hh.2.1).hasDerivAt
      have hc := hd₂.comp t ((hasDerivAt_id t).const_sub S)
      convert! hd₁.add hc using 1
      simp only [mul_neg_one,sub_eq_add_neg]
    have hmono : StrictMonoOn g (Icc m₁ m₂) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      · intro t ht
        exact (hdiff t ht).continuousAt.continuousWithinAt
      · intro t ht
        have hti : t ∈ Icc m₁ m₂ := interior_subset ht
        rw [(hdiff t hti).deriv]
        have hh := hcell t hti
        exact (allBranchExterior_positive_slope_ratio B ε a σ t (S-t) hε hεr ha hσ hsmall₁ hsmall₂
          hh.1 hh.2.1 hh.2.2.1 hh.2.2.2).1
    have hh := hmono (left_mem_Icc.mpr hm.le) (right_mem_Icc.mpr hm.le) hm
    have hS₁ : S-m₁=M₁ := by dsimp [S]; ring
    have hS₂ : S-m₂=M₂ := by dsimp [S]; linarith
    simpa only [g,hS₁,hS₂] using hh
  intro x hx y hy he
  have hF : x.1+x.2=y.1+y.2 := by
    have hh := congrArg Prod.fst he
    dsimp [allBranchExteriorPositivePhase] at hh
    linarith
  have hG : originalRealPhase d ε x.1+originalRealPhase d ε x.2=
      originalRealPhase d ε y.1+originalRealPhase d ε y.2 := by
    have hh := congrArg Prod.snd he
    dsimp [allBranchExteriorPositivePhase] at hh
    linarith
  have hxy : x.1=y.1 := by
    rcases lt_trichotomy x.1 y.1 with h|h|h
    · exact False.elim ((ne_of_lt (hord x.1 x.2 y.1 y.2 hx hy h hF)) hG)
    · exact h
    · exact False.elim ((ne_of_lt (hord y.1 y.2 x.1 x.2 hy hx h hF.symm)) hG.symm)
  exact Prod.ext hxy (by linarith)

theorem allBranchExterior_positive_phase_image {d : LocalBranchData} (B : BranchEstimates d)
    (ε a σ F₀ G₀ : ℝ) (hε : 0 < ε) (hεr : ε ≤ B.ε₀) (ha : 0 < a) (hσ : 0 < σ) :
    allBranchExteriorPositivePhase d ε F₀ G₀ '' allBranchExteriorPositiveRegion B.r a σ ⊆
      Icc (F₀,G₀) (F₀+2*B.r,G₀+Real.pi) := by
  rintro z ⟨x,hx,rfl⟩
  have hm : x.1 ≤ B.r := by linarith [hx.2.1,hx.2.2.2]
  have hM : 0 ≤ x.2 := by linarith [hx.2.2.1]
  obtain ⟨hr₁,hi₁⟩ := B.quadrant ε x.1 hε hεr (by simpa [abs_of_nonneg hx.1] using hm)
  obtain ⟨hr₂,hi₂⟩ := B.quadrant ε x.2 hε hεr (by simpa [abs_of_nonneg hM] using hx.2.1)
  have hs₁ := lowerArccos_sheet _ hr₁ hi₁
  have hs₂ := lowerArccos_sheet _ hr₂ hi₂
  change (F₀ ≤ x.1+x.2+F₀ ∧ G₀ ≤ originalRealPhase d ε x.1+originalRealPhase d ε x.2+G₀) ∧
    x.1+x.2+F₀ ≤ F₀+2*B.r ∧ originalRealPhase d ε x.1+originalRealPhase d ε x.2+G₀ ≤ G₀+Real.pi
  have hp₁ : 0 < originalRealPhase d ε x.1 ∧ originalRealPhase d ε x.1 < Real.pi/2 := ⟨hs₁.2.1,hs₁.2.2.1⟩
  have hp₂ : 0 < originalRealPhase d ε x.2 ∧ originalRealPhase d ε x.2 < Real.pi/2 := ⟨hs₂.2.1,hs₂.2.2.1⟩
  constructor <;> constructor <;> linarith [hx.1,hx.2.1]

end
end IsingBulk.Tail
