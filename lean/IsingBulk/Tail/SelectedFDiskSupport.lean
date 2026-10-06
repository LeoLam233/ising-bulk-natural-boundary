import IsingBulk.Tail.SelectedFContinuationCompact
import IsingBulk.Tail.SelectedFDiskBranch
import IsingBulk.Tail.RootAttenuation
import IsingBulk.Tail.SelectorWeights

/-! Attachment of the constructed lower chord core to the actual local
branch coordinate, with one geometric width fixed before N and occupancy. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter Metric
open scoped Topology

theorem lowerChord_zero_angle {b θ : ℝ} (hb : 0 < b) (hbπ : b < Real.pi)
    (hθ0 : 0 ≤ θ) (hθπ : θ ≤ 2*Real.pi) (hch : lowerChord b θ=0) :
    θ=2*Real.pi-b := by
  have hsinb := Real.sin_pos_of_pos_of_lt_pi hb hbπ
  have hc : Real.cos θ=Real.cos b := by
    unfold lowerChord at hch
    nlinarith [sq_nonneg (Real.sin θ+Real.sin b),sq_nonneg (Real.cos θ-Real.cos b)]
  have hs : Real.sin θ = -Real.sin b := by
    unfold lowerChord at hch
    nlinarith [sq_nonneg (Real.sin θ+Real.sin b),sq_nonneg (Real.cos θ-Real.cos b)]
  have hθlow : Real.pi < θ := by
    by_contra h
    have hh := Real.sin_nonneg_of_nonneg_of_le_pi hθ0 (le_of_not_gt h)
    linarith
  have hm : 2*Real.pi-θ ∈ Icc 0 Real.pi := ⟨by linarith,by linarith⟩
  have hbmem : b ∈ Icc 0 Real.pi := ⟨hb.le,hbπ.le⟩
  have he := Real.strictAntiOn_cos.injOn hm hbmem (by simpa only [Real.cos_two_pi_sub] using hc)
  linarith

theorem lowerChord_small_coordinate {b r : ℝ} (hb : 0 < b) (hbπ : b < Real.pi) (hr : 0 < r) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ θ : ℝ, 0 ≤ θ → θ ≤ 2*Real.pi →
      lowerChord b θ ≤ η₀^2 → |θ+b-2*Real.pi| < r := by
  let K : Set ℝ := Icc 0 (2*Real.pi) ∩ {θ | r ≤ |θ+b-2*Real.pi|}
  have hK : IsCompact K := isCompact_Icc.inter_right (isClosed_le continuous_const (by fun_prop))
  have hc : Continuous (lowerChord b) := by unfold lowerChord; fun_prop
  by_cases hn : K.Nonempty
  · obtain ⟨θ,hθ,hmin⟩ := hK.exists_isMinOn hn hc.continuousOn
    have hp : 0 < lowerChord b θ := by
      have hnon : 0 ≤ lowerChord b θ := by unfold lowerChord; positivity
      have hne : lowerChord b θ ≠ 0 := by
        intro hz
        have he := lowerChord_zero_angle hb hbπ hθ.1.1 hθ.1.2 hz
        have hh : r ≤ |θ+b-2*Real.pi| := hθ.2
        rw [he] at hh
        have he0 : 2*Real.pi-b+b-2*Real.pi=0 := by ring
        rw [he0,abs_zero] at hh
        linarith
      exact lt_of_le_of_ne hnon hne.symm
    refine ⟨Real.sqrt (lowerChord b θ)/2,by positivity,?_⟩
    intro u hu0 huπ hu
    by_contra h
    have hmem : u ∈ K := ⟨⟨hu0,huπ⟩,le_of_not_gt h⟩
    have hmin' : lowerChord b θ ≤ lowerChord b u := hmin hmem
    have hs := Real.sq_sqrt hp.le
    nlinarith
  · refine ⟨1,by norm_num,?_⟩
    intro θ hθ0 hθπ _hch
    by_contra h
    exact hn ⟨θ,⟨hθ0,hθπ⟩,le_of_not_gt h⟩

theorem constructed_lower_core_plateau {b η α θ : ℝ}
    (hb : 0 < Real.sin b) (hη : 0 < η) (hηsmall : η ≤ Real.sin b/4) (hα : 0 < α)
    (hcore : lowerChord b θ ≤ η^2) :
    (constructedSelector b η α).m θ=1 ∧ (constructedSelector b η α).p θ=0 := by
  have hm : periodicLowerM b η θ=1 := by
    apply Real.smoothTransition.one_of_one_le
    have hd := (div_le_one (sq_pos_of_pos hη)).mpr hcore
    linarith
  refine ⟨hm,?_⟩
  have hs : Real.sin θ < 0 := by
    by_contra hn
    have hz := lowerM_zero_of_nonneg_sine b η θ hb hη hηsmall (le_of_not_gt hn)
    rw [hm] at hz
    norm_num at hz
  exact thresholdStep_zero (by linarith) (by linarith)

theorem deformedPoint_selected_formula {N : ℕ} (f : SelectorFunctions) (c₀ eps τ : ℝ)
    (θ : Fin N → ℝ) (i : Fin N) :
    deformedPoint f (Real.exp (-c₀*eps)) τ 1 θ i =
      radialAnglePoint (-c₀*eps+selectedLimitingShift f τ
        (occupancy (fun j => f.p (θ j))/(N:ℝ)) (θ i)) (θ i) := by
  rw [deformedPoint_polar f (Real.exp_pos _)]
  have hh : retractionShift τ (fun j => f.p (θ j)) (fun j => f.m (θ j)) i =
      selectedLimitingShift f τ (occupancy (fun j => f.p (θ j))/(N:ℝ)) (θ i) := by
    simp only [retractionShift,selectedLimitingShift,div_eq_mul_inv,mul_inv_rev]
    ring
  simp only [Real.log_exp,one_mul,hh,radialAnglePoint]

theorem deformedPoint_selected_plateau {N : ℕ} (f : SelectorFunctions) (b c₀ eps τ : ℝ)
    (θ : Fin N → ℝ) (i : Fin N) (hp : f.p (θ i)=0) (hm : f.m (θ i)=1) :
    deformedPoint f (Real.exp (-c₀*eps)) τ 1 θ i =
      plateauY c₀ eps τ (occupancy (fun j => f.p (θ j))/(N:ℝ)) b (θ i+b-2*Real.pi) := by
  rw [deformedPoint_selected_formula]
  have ha : -b+(θ i+b-2*Real.pi)=θ i-2*Real.pi := by ring
  simp only [selectedLimitingShift,hp,hm,mul_zero,mul_one,zero_add,plateauY,ha,
    radialAnglePoint,Complex.exp_add]
  congr 1
  · congr 2
    ring
  · simp only [Complex.exp_ofReal_mul_I,Real.cos_sub_two_pi,Real.sin_sub_two_pi]

theorem deformedPoint_selected_anchor {N : ℕ} (f : SelectorFunctions) (c₀ eps τ : ℝ)
    (θ : Fin N → ℝ) (q : Fin N) (hp : f.p (θ q)=1) (hm : f.m (θ q)=0) :
    deformedPoint f (Real.exp (-c₀*eps)) τ 1 θ q = upperAnchorY c₀ eps τ 1 (θ q) := by
  rw [deformedPoint_selected_formula]
  simp only [selectedLimitingShift,hp,hm,mul_zero,zero_div,add_zero,mul_one,
    upperAnchorY,radialAnglePoint]
  congr 2
  push_cast
  ring

theorem selected_named_compact_chord {b η α θ : ℝ} (hb : 0 < Real.sin b)
    (hη : 0 ≤ η) (hηsmall : η ≤ Real.sin b/4) (hα : 0 < α)
    (ha : periodicUpperA α θ ≠ 0) : η^2/2 ≤ lowerChord b θ := by
  have hs := upperA_support_sine α hα (show θ ∈ tsupport (periodicUpperA α) from subset_closure ha)
  change α ≤ Real.sin θ at hs
  unfold lowerChord
  nlinarith [sq_nonneg (Real.cos θ-Real.cos b),sq_nonneg (Real.sin θ),
    mul_nonneg (show 0 ≤ Real.sin θ by linarith) hb.le]

theorem selected_tsupport_named {N : ℕ} (f : SelectorFunctions) (θ : Fin N → ℝ)
    (hθ : θ ∈ tsupport (fun θ : Fin N → ℝ => 1-angularSelector f θ)) :
    ∃ q : Fin N, θ q ∈ tsupport f.a := by
  have hclosed : IsClosed {θ : Fin N → ℝ | ∃ q : Fin N, θ q ∈ tsupport f.a} := by
    have hh := isClosed_iUnion_of_finite (fun q : Fin N =>
      (isClosed_tsupport f.a).preimage (continuous_apply q))
    convert hh using 1
    ext θ
    simp
  have hsub : tsupport (fun θ : Fin N → ℝ => 1-angularSelector f θ) ⊆
      {θ : Fin N → ℝ | ∃ q : Fin N, θ q ∈ tsupport f.a} := by
    apply closure_minimal _ hclosed
    intro θ hθ'
    obtain ⟨q,hq⟩ := selected_exists_named f θ hθ'
    exact ⟨q,subset_closure hq⟩
  exact hsub hθ

theorem constructed_named_support {b η α θ : ℝ} (hb : 0 < Real.sin b)
    (hη : 0 < η) (hηsmall : η ≤ Real.sin b/4) (hα : 0 < α)
    (ha : θ ∈ tsupport (periodicUpperA α)) :
    (constructedSelector b η α).p θ=1 ∧ (constructedSelector b η α).m θ=0 ∧
      α ≤ Real.sin θ ∧ η^2/2 ≤ lowerChord b θ := by
  have hp := (upperP_plateau_on_a_support α hα θ ha).eq_of_nhds
  have hm := (lowerM_zero_near_a_support b η α θ hb hη hηsmall hα ha).eq_of_nhds
  have hs : α ≤ Real.sin θ := upperA_support_sine α hα ha
  refine ⟨hp,hm,hs,?_⟩
  unfold lowerChord
  nlinarith [sq_nonneg (Real.cos θ-Real.cos b),sq_nonneg (Real.sin θ),
    mul_nonneg (show 0 ≤ Real.sin θ by linarith) hb.le]

end
end IsingBulk.Tail
