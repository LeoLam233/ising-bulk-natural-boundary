import IsingBulk.Tail.SelectedFContinuationLimiting
import IsingBulk.First.RadialDiskAdmissibility
import Mathlib.Topology.Compactness.Compact

/-! Constructed compact cover of actual regular selected-contour roots.
The occupancy fraction is a compact argument of the exact coupled formula;
no integral treats it as an independent integration variable. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter Metric
open scoped Topology

def selectedCompactParameters (b η : ℝ) : Set (ℝ × ℝ) :=
  Icc 0 1 ×ˢ (Icc 0 (2*Real.pi) ∩ {θ | η^2/2 ≤ lowerChord b θ})

theorem selectedCompactParameters_compact (b η : ℝ) :
    IsCompact (selectedCompactParameters b η) := by
  apply isCompact_Icc.prod
  apply isCompact_Icc.inter_right
  exact isClosed_le continuous_const (by unfold lowerChord; fun_prop)

theorem constructed_selectedLimitingW_domain {b η α τ : ℝ}
    (hb : 0 < Real.sin b) (hη : 0 < η) (hηsmall : η ≤ Real.sin b/4)
    (hα : 0 < α) (hαsmall : α < Real.sin b/4)
    (hτ : 0 < τ) (hτsmall : 2*τ ≤ 1) (hτS : 4*τ < 1+Real.cos b)
    {p : ℝ × ℝ} (hp : p ∈ selectedCompactParameters b η) :
    selectedLimitingW (1+Real.cos b) (constructedSelector b η α) τ p.1 p.2 ∈ continuedRootDomain := by
  have hp0 := (thresholdStep_range (α/2) (3*α/4) (Real.sin p.2)).1
  have hp1 := (thresholdStep_range (α/2) (3*α/4) (Real.sin p.2)).2
  have hm0 := Real.smoothTransition.nonneg (2-lowerChord b p.2/η^2)
  have hm1 := Real.smoothTransition.le_one (2-lowerChord b p.2/η^2)
  apply selectedLimitingW_domain b (constructedSelector b η α) hτ hτsmall hτS
    hp.1.1 hp.1.2 hb hp0 hp1 hm0 hm1
  · intro hs
    exact thresholdStep_zero (by linarith) (by linarith)
  · intro hs
    exact lowerM_zero_of_nonneg_sine b η p.2 hb hη hηsmall hs
  · intro hs
    apply thresholdStep_one (by linarith)
    rw [hs]
    linarith
  · have hh : η^2/2 ≤ lowerChord b p.2 := hp.2.2
    intro he
    rw [he] at hh
    nlinarith [sq_pos_of_pos hη]

def selectedCenterW (theta c₀ : ℝ) (f : SelectorFunctions) (τ : ℝ)
    (eps ρ u : ℝ) : ℂ :=
  sourceW (radialParameter theta eps)
    (radialAnglePoint (-c₀*eps+selectedLimitingShift f τ ρ u) u)

theorem selectedCenterW_continuousAt (theta c₀ τ : ℝ) (f : SelectorFunctions)
    (hp : Continuous f.p) (hm : Continuous f.m) {q : ℝ × (ℝ × ℝ)} (hq : 0 ≤ q.1) :
    ContinuousAt (fun p : ℝ × (ℝ × ℝ) => selectedCenterW theta c₀ f τ p.1 p.2.1 p.2.2) q := by
  have hs : Continuous (fun p : ℝ × (ℝ × ℝ) => radialParameter theta p.1) := by
    unfold radialParameter
    fun_prop
  have hs0 : radialParameter theta q.1 ≠ 0 := norm_ne_zero_iff.mp (by
    rw [radialParameter_norm hq]
    linarith)
  have hy : Continuous (fun p : ℝ × (ℝ × ℝ) =>
      radialAnglePoint (-c₀*p.1+selectedLimitingShift f τ p.2.1 p.2.2) p.2.2) := by
    unfold radialAnglePoint selectedLimitingShift
    fun_prop
  have hy0 : radialAnglePoint (-c₀*q.1+selectedLimitingShift f τ q.2.1 q.2.2) q.2.2 ≠ 0 :=
    Complex.exp_ne_zero _
  unfold selectedCenterW sourceW sourceS
  exact (hs.continuousAt.add (hs.continuousAt.inv₀ hs0)).sub
    ((hy.continuousAt.add (hy.continuousAt.inv₀ hy0)).div_const 2)

theorem selectedCenterW_zero {theta b : ℝ} (hrel : Real.cos b=2*Real.cos theta-1)
    (c₀ : ℝ) (f : SelectorFunctions) (τ ρ u : ℝ) :
    selectedCenterW theta c₀ f τ 0 ρ u = selectedLimitingW (1+Real.cos b) f τ ρ u := by
  have ht : sourceS (radialParameter theta 0) = ((1+Real.cos b:ℝ):ℂ) := by
    have hh := radial_trace_components theta 0 (by norm_num)
    apply Complex.ext
    · change (radialParameter theta 0+(radialParameter theta 0)⁻¹).re = _
      rw [hh.1]
      simp only [Complex.ofReal_re]
      linarith
    · change (radialParameter theta 0+(radialParameter theta 0)⁻¹).im = _
      rw [hh.2]
      simp
  simp only [selectedCenterW,mul_zero,zero_add,sourceW,ht,
    selectedLimitingW,radialAnglePoint,Complex.cosh,← Complex.exp_neg]

/-- All compact continued roots for small actual radial epsilon are in a
single constructed compact subset of the regular root domain, uniformly in
angle and occupancy fraction. -/
theorem selected_regular_center_compact {theta b η α τ c₀ : ℝ}
    (hrel : Real.cos b=2*Real.cos theta-1)
    (hb : 0 < Real.sin b) (hη : 0 < η) (hηsmall : η ≤ Real.sin b/4)
    (hα : 0 < α) (hαsmall : α < Real.sin b/4)
    (hτ : 0 < τ) (hτsmall : 2*τ ≤ 1) (hτS : 4*τ < 1+Real.cos b) :
    ∃ eps₀ : ℝ, 0 < eps₀ ∧ eps₀ ≤ 1 ∧ ∃ K : Set ℂ, IsCompact K ∧
      K ⊆ continuedRootDomain ∧ ∀ eps : ℝ, 0 ≤ eps → eps ≤ eps₀ →
        ∀ p ∈ selectedCompactParameters b η,
          selectedCenterW theta c₀ (constructedSelector b η α) τ eps p.1 p.2 ∈ K := by
  let f := constructedSelector b η α
  let F : ℝ × (ℝ × ℝ) → ℂ := fun q => selectedCenterW theta c₀ f τ q.1 q.2.1 q.2.2
  have hp : Continuous f.p := (periodicUpperP_smooth α).continuous
  have hm : Continuous f.m := (periodicLowerM_smooth b η).continuous
  have hD : ∀ p ∈ selectedCompactParameters b η, F (0,p) ∈ continuedRootDomain := by
    intro p hp
    dsimp only [F]
    rw [selectedCenterW_zero hrel]
    exact constructed_selectedLimitingW_domain hb hη hηsmall hα hαsmall hτ hτsmall hτS hp
  have hnear : ∀ᶠ eps : ℝ in 𝓝 0, ∀ p ∈ selectedCompactParameters b η,
      F (eps,p) ∈ continuedRootDomain := by
    apply (selectedCompactParameters_compact b η).eventually_forall_of_forall_eventually
    intro p hp'
    exact (selectedCenterW_continuousAt theta c₀ τ f hp hm (q := (0,p)) (by norm_num)).eventually
      (continuedRootDomain_isOpen.mem_nhds (hD p hp'))
  obtain ⟨d,hd,hdb⟩ := Metric.mem_nhds_iff.mp hnear
  let eps₀ := min (d/2) 1
  have heps : 0 < eps₀ := lt_min (by positivity) zero_lt_one
  let T : Set (ℝ × (ℝ × ℝ)) := Icc 0 eps₀ ×ˢ selectedCompactParameters b η
  have hT : IsCompact T := isCompact_Icc.prod (selectedCompactParameters_compact b η)
  have hF : ContinuousOn F T := by
    intro q hq
    exact (selectedCenterW_continuousAt theta c₀ τ f hp hm hq.1.1).continuousWithinAt
  refine ⟨eps₀,heps,min_le_right _ _,F '' T,hT.image_of_continuousOn hF,?_,?_⟩
  · rintro W ⟨q,hq,rfl⟩
    apply hdb (show q.1 ∈ ball (0:ℝ) d from ?_) q.2 hq.2
    rw [mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg hq.1.1]
    have hle : q.1 ≤ d/2 := hq.1.2.trans (min_le_left _ _)
    linarith
  · intro eps h0 h1 p hp'
    exact ⟨(eps,p),⟨⟨h0,h1⟩,hp'⟩,rfl⟩

end
end IsingBulk.Tail
