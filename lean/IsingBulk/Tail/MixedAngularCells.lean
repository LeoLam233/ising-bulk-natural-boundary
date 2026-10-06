import IsingBulk.Tail.MixedPositiveGlobalIntegral
import IsingBulk.Tail.MixedSourcePlateaus

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter
open scoped Topology BigOperators

/-- Compact scalar anchor sets admit a finite interval cover inside their
open geometric margin. The cover is chosen before the particle number. -/
theorem finite_closed_interval_cover {K U : Set ℝ} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K⊆U) :
    ∃ T : Finset (ℝ×ℝ), (∀ I∈T,Icc I.1 I.2⊆U) ∧
      ∀ x∈K,∃ I∈T,x∈Icc I.1 I.2 := by
  classical
  have hloc (x : K) := exists_Icc_mem_subset_of_mem_nhds (hU.mem_nhds (hKU x.2))
  choose l r _hmem hnhds hsub using hloc
  obtain ⟨t,ht⟩ := hK.elim_nhds_subcover' (fun x hx => Icc (l ⟨x,hx⟩) (r ⟨x,hx⟩))
    (fun x hx => hnhds ⟨x,hx⟩)
  refine ⟨t.image (fun x => (l x,r x)),?_,?_⟩
  · intro I hI
    obtain ⟨x,_hx,rfl⟩ := Finset.mem_image.mp hI
    exact hsub x
  · intro x hx
    obtain ⟨y,hyt,hy⟩ := mem_iUnion₂.mp (ht hx)
    exact ⟨(l y,r y),Finset.mem_image.mpr ⟨y,hyt,rfl⟩,hy⟩

def mixedAngularCell {N : ℕ} (j q : Fin N) (a b : ℝ×ℝ) : Set (Fin N → ℝ) :=
  angleBox N ∩ {θ | θ j∈Icc a.1 a.2} ∩ {θ | θ q∈Icc b.1 b.2}

theorem mixedAngularCell_measurable {N : ℕ} (j q : Fin N) (a b : ℝ×ℝ) :
    MeasurableSet (mixedAngularCell j q a b) := by
  apply MeasurableSet.inter
  · exact measurableSet_Icc.inter (measurableSet_Icc.preimage (measurable_pi_apply j))
  · exact measurableSet_Icc.preimage (measurable_pi_apply q)

theorem mixedAngularCell_convex {N : ℕ} (j q : Fin N) (a b : ℝ×ℝ) :
    Convex ℝ (mixedAngularCell j q a b) := by
  exact ((convex_Icc _ _).inter ((convex_Icc _ _).linear_preimage (LinearMap.proj j))).inter
    ((convex_Icc _ _).linear_preimage (LinearMap.proj q))

theorem mixed_original_anchor_cover (b outer : ℝ) (ho : 0<outer) :
    ∃ T : Finset (ℝ×ℝ),
      (∀ I∈T,∀ x∈Icc I.1 I.2,outer/4 < |sectorDisplacement b x|) ∧
      ∀ x∈Icc 0 (2*Real.pi),outer/2 ≤ |sectorDisplacement b x| →
        ∃ I∈T,x∈Icc I.1 I.2 := by
  let K := Icc 0 (2*Real.pi) ∩ {x | outer/2 ≤ |sectorDisplacement b x|}
  let U := {x : ℝ | outer/4 < |sectorDisplacement b x|}
  have hc : Continuous (fun x => |sectorDisplacement b x|) := by unfold sectorDisplacement; fun_prop
  have hK : IsCompact K := isCompact_Icc.inter_right (isClosed_le continuous_const hc)
  have hKU : K⊆U := by
    intro x hx
    have hg : outer/2≤|sectorDisplacement b x| := hx.2
    change outer/4 < |sectorDisplacement b x|
    linarith
  obtain ⟨T,hT,hcover⟩ := finite_closed_interval_cover hK (isOpen_lt continuous_const hc) hKU
  exact ⟨T,hT,fun x hx hgap => hcover x ⟨hx,hgap⟩⟩

/-- The named-current scalar support is covered inside the genuine upper
plateau and a fixed profile gap, including its support endpoints. -/
theorem mixed_current_anchor_cover {b α : ℝ} (hb : 0<Real.sin b)
    (hα : 0<α) (hαsmall : α<Real.sin b/4) :
    ∃ T : Finset (ℝ×ℝ),
      (∀ I∈T,∀ x∈Icc I.1 I.2,
        3*α/4<Real.sin x ∧ (Real.sin b)^2/8 < |sectorDisplacement b x|) ∧
      ∀ x∈Icc 0 (2*Real.pi),α≤Real.sin x → Real.sin x≤3*α/2 →
        ∃ I∈T,x∈Icc I.1 I.2 := by
  let K := Icc 0 (2*Real.pi) ∩ {x | α≤Real.sin x ∧ Real.sin x≤3*α/2}
  let U := {x : ℝ | 3*α/4<Real.sin x ∧ (Real.sin b)^2/8 < |sectorDisplacement b x|}
  have hc : Continuous (fun x => |sectorDisplacement b x|) := by unfold sectorDisplacement; fun_prop
  have hK : IsCompact K := isCompact_Icc.inter_right
    ((isClosed_le continuous_const Real.continuous_sin).inter
      (isClosed_le Real.continuous_sin continuous_const))
  have hU : IsOpen U := (isOpen_lt continuous_const Real.continuous_sin).inter
    (isOpen_lt continuous_const hc)
  have hKU : K⊆U := by
    intro x hx
    have hg := named_current_outer_profile hb hα hαsmall hx.2.1 hx.2.2
    exact ⟨by linarith [hx.2.1],by nlinarith⟩
  obtain ⟨T,hT,hcover⟩ := finite_closed_interval_cover hK hU hKU
  exact ⟨T,hT,fun x hx hlo hhi => hcover x ⟨hx,hlo,hhi⟩⟩

theorem mixed_upper_open_plateau_germ {b η α x : ℝ}
    (hb : 0<Real.sin b) (hη : 0<η) (hηsmall : η≤Real.sin b/4) (hα : 0<α)
    (hx : 3*α/4<Real.sin x) :
    (constructedSelector b η α).p =ᶠ[𝓝 x] (fun _ => 1) ∧
    (constructedSelector b η α).m =ᶠ[𝓝 x] (fun _ => 0) := by
  have he := Real.continuous_sin.continuousAt.eventually (Ioi_mem_nhds hx)
  constructor
  · filter_upwards [he] with t ht
    exact thresholdStep_one (by linarith) ht.le
  · filter_upwards [he] with t ht
    exact lowerM_zero_of_nonneg_sine b η t hb hη hηsmall (by linarith)

end
end IsingBulk.Tail
