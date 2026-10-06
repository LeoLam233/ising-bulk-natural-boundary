import IsingBulk.Tail.SelectedFContinuationCompact

/-! The actual current-support compact cover, uniform down to lambda=0.
The upper branch is excluded by the fixed selector support, while the true
lower branch core is removed before the compact cover is selected. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter Metric
open scoped Topology

 def currentCompactParameters (b η α : ℝ) : Set (ℝ × (ℝ × ℝ)) :=
  Icc 0 1 ×ˢ (selectedCompactParameters b η ∩ {p | Real.sin p.2 ≤ 3*α/2})

 theorem currentCompactParameters_compact (b η α : ℝ) : IsCompact (currentCompactParameters b η α) := by
  apply isCompact_Icc.prod
  exact (selectedCompactParameters_compact b η).inter_right
    (isClosed_le (Real.continuous_sin.comp continuous_snd) continuous_const)

 theorem current_unshifted_regular_domain {b η α θ : ℝ}
    (hb : 0 < Real.sin b) (hS : 0 < 1+Real.cos b) (hη : 0 < η)
    (hαsmall : α < Real.sin b/4) (hθ : Real.sin θ ≤ 3*α/2)
    (hcore : η^2/2 ≤ lowerChord b θ) : ((1+Real.cos b-Real.cos θ:ℝ):ℂ) ∈ continuedRootDomain := by
  have hlo : -1 < 1+Real.cos b-Real.cos θ := by linarith [Real.cos_le_one θ]
  have hne : 1+Real.cos b-Real.cos θ ≠ 1 := by
    intro he
    have hc : Real.cos θ=Real.cos b := by linarith
    have hsin : (Real.sin θ-Real.sin b)*(Real.sin θ+Real.sin b)=0 := by
      have hθ' := Real.sin_sq_add_cos_sq θ
      have hb' := Real.sin_sq_add_cos_sq b
      rw [hc] at hθ'
      nlinarith
    rcases mul_eq_zero.mp hsin with hp | hm
    · have hs := sub_eq_zero.mp hp
      linarith
    · have hs : Real.sin θ = -Real.sin b := by linarith
      have hz : lowerChord b θ=0 := by simp [lowerChord,hc,hs]
      rw [hz] at hcore
      nlinarith [sq_pos_of_pos hη]
  by_cases hh : 1 < 1+Real.cos b-Real.cos θ
  · exact Or.inl (Or.inr hh)
  · exact Or.inr (abs_lt.mpr ⟨hlo,lt_of_le_of_ne (le_of_not_gt hh) hne⟩)

 theorem constructed_current_limiting_domain {b η α τ : ℝ}
    (hb : 0 < Real.sin b) (hη : 0 < η) (hηsmall : η ≤ Real.sin b/4)
    (hα : 0 < α) (hαsmall : α < Real.sin b/4)
    (hτ : 0 < τ) (hτsmall : 2*τ ≤ 1) (hτS : 4*τ < 1+Real.cos b)
    {p : ℝ × (ℝ × ℝ)} (hp : p ∈ currentCompactParameters b η α) :
    selectedLimitingW (1+Real.cos b) (constructedSelector b η α) (p.1*τ) p.2.1 p.2.2 ∈ continuedRootDomain := by
  by_cases hlam : 0 < p.1
  · have hlamtau : 0 < p.1*τ := mul_pos hlam hτ
    have hlamtaule : p.1*τ ≤ τ := mul_le_of_le_one_left hτ.le hp.1.2
    exact constructed_selectedLimitingW_domain hb hη hηsmall hα hαsmall hlamtau
      (by linarith) (by linarith) hp.2.1
  · have hlam0 : p.1=0 := le_antisymm (le_of_not_gt hlam) hp.1.1
    have he : selectedLimitingW (1+Real.cos b) (constructedSelector b η α) (p.1*τ) p.2.1 p.2.2 =
        ((1+Real.cos b-Real.cos p.2.2:ℝ):ℂ) := by
      simp [selectedLimitingW,selectedLimitingShift,hlam0,Complex.cosh_mul_I,← Complex.ofReal_cos]
    rw [he]
    exact current_unshifted_regular_domain hb (by linarith) hη hαsmall hp.2.2 hp.2.1.2.2

 theorem currentCenterW_continuousAt (theta c₀ τ : ℝ) (f : SelectorFunctions)
    (hp : Continuous f.p) (hm : Continuous f.m) {q : ℝ × (ℝ × (ℝ × ℝ))} (hq : 0 ≤ q.1) :
    ContinuousAt (fun p : ℝ × (ℝ × (ℝ × ℝ)) =>
      selectedCenterW theta c₀ f (p.2.1*τ) p.1 p.2.2.1 p.2.2.2) q := by
  have hs : Continuous (fun p : ℝ × (ℝ × (ℝ × ℝ)) => radialParameter theta p.1) := by
    unfold radialParameter
    fun_prop
  have hs0 : radialParameter theta q.1 ≠ 0 := norm_ne_zero_iff.mp (by
    rw [radialParameter_norm hq]
    linarith)
  have hy : Continuous (fun p : ℝ × (ℝ × (ℝ × ℝ)) =>
      radialAnglePoint (-c₀*p.1+selectedLimitingShift f (p.2.1*τ) p.2.2.1 p.2.2.2) p.2.2.2) := by
    unfold radialAnglePoint selectedLimitingShift
    fun_prop
  have hy0 : radialAnglePoint (-c₀*q.1+selectedLimitingShift f (q.2.1*τ) q.2.2.1 q.2.2.2) q.2.2.2 ≠ 0 :=
    Complex.exp_ne_zero _
  unfold selectedCenterW sourceW sourceS
  exact (hs.continuousAt.add (hs.continuousAt.inv₀ hs0)).sub
    ((hy.continuousAt.add (hy.continuousAt.inv₀ hy0)).div_const 2)

 theorem current_regular_center_compact {theta b η α τ c₀ : ℝ}
    (hrel : Real.cos b=2*Real.cos theta-1)
    (hb : 0 < Real.sin b) (hη : 0 < η) (hηsmall : η ≤ Real.sin b/4)
    (hα : 0 < α) (hαsmall : α < Real.sin b/4)
    (hτ : 0 < τ) (hτsmall : 2*τ ≤ 1) (hτS : 4*τ < 1+Real.cos b) :
    ∃ eps₀ : ℝ, 0 < eps₀ ∧ eps₀ ≤ 1 ∧ ∃ K : Set ℂ, IsCompact K ∧ K ⊆ continuedRootDomain ∧
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ eps₀ → ∀ p ∈ currentCompactParameters b η α,
        selectedCenterW theta c₀ (constructedSelector b η α) (p.1*τ) eps p.2.1 p.2.2 ∈ K := by
  let f := constructedSelector b η α
  let F : ℝ × (ℝ × (ℝ × ℝ)) → ℂ := fun q =>
    selectedCenterW theta c₀ f (q.2.1*τ) q.1 q.2.2.1 q.2.2.2
  have hp : Continuous f.p := (periodicUpperP_smooth α).continuous
  have hm : Continuous f.m := (periodicLowerM_smooth b η).continuous
  have hD : ∀ p ∈ currentCompactParameters b η α, F (0,p) ∈ continuedRootDomain := by
    intro p hp'
    dsimp only [F]
    rw [selectedCenterW_zero hrel]
    exact constructed_current_limiting_domain hb hη hηsmall hα hαsmall hτ hτsmall hτS hp'
  have hnear : ∀ᶠ eps : ℝ in 𝓝 0, ∀ p ∈ currentCompactParameters b η α,
      F (eps,p) ∈ continuedRootDomain := by
    apply (currentCompactParameters_compact b η α).eventually_forall_of_forall_eventually
    intro p hp'
    exact (currentCenterW_continuousAt theta c₀ τ f hp hm (q := (0,p)) (by norm_num)).eventually
      (continuedRootDomain_isOpen.mem_nhds (hD p hp'))
  obtain ⟨d,hd,hdb⟩ := Metric.mem_nhds_iff.mp hnear
  let eps₀ := min (d/2) 1
  let T : Set (ℝ × (ℝ × (ℝ × ℝ))) := Icc 0 eps₀ ×ˢ currentCompactParameters b η α
  have hT : IsCompact T := isCompact_Icc.prod (currentCompactParameters_compact b η α)
  have hF : ContinuousOn F T := by
    intro q hq
    exact (currentCenterW_continuousAt theta c₀ τ f hp hm hq.1.1).continuousWithinAt
  refine ⟨eps₀,lt_min (by positivity) zero_lt_one,min_le_right _ _,F '' T,
    hT.image_of_continuousOn hF,?_,?_⟩
  · rintro W ⟨q,hq,rfl⟩
    apply hdb (show q.1 ∈ ball (0:ℝ) d from ?_) q.2 hq.2
    rw [mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg hq.1.1]
    have hle : q.1 ≤ d/2 := hq.1.2.trans (min_le_left _ _)
    linarith
  · intro eps h0 h1 p hp'
    exact ⟨(eps,p),⟨⟨h0,h1⟩,hp'⟩,rfl⟩

end
end IsingBulk.Tail
