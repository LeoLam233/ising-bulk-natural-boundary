import IsingBulk.Joint.Geometry.Plurisubharmonic
import IsingBulk.Joint.Geometry.Components

namespace IsingBulk.Joint
noncomputable section
open Set Metric

/-- Pseudoconvexity witnessed by a continuous plurisubharmonic proper exhaustion. -/
def IsPseudoconvex (D : Set Coupling) : Prop :=
  ∃ φ : Coupling → ℝ, IsPlurisubharmonicOn φ D ∧
    ∀ r : ℝ, IsCompact {K | K ∈ D ∧ φ K ≤ r}

theorem spectralExhaustion_gap_bound {K : Coupling} (hK : K ∉ spectralSet)
    {r : ℝ} (hr : spectralExhaustion K ≤ r) : Real.exp (-r) ≤ spectralGap K := by
  have hp := (spectralGap_pos_iff K).mpr hK
  have hb : -Real.log (spectralGap K) ≤ spectralExhaustion K := by
    have h := le_max_right (0 : ℝ) (-Real.log (spectralGap K))
    dsimp [spectralExhaustion,spectralBarrier]
    nlinarith [sq_nonneg ‖K.1‖,sq_nonneg ‖K.2‖]
  calc Real.exp (-r) ≤ Real.exp (Real.log (spectralGap K)) := Real.exp_le_exp.mpr (by linarith)
       _ = spectralGap K := Real.exp_log hp

theorem spectralExhaustion_sublevel_isClosed (r : ℝ) :
    IsClosed {K | K ∉ spectralSet ∧ spectralExhaustion K ≤ r} := by
  let L : Set Coupling := {K | Real.exp (-r) ≤ spectralGap K}
  have hL : IsClosed L := isClosed_le continuous_const spectralGap_continuous
  have hLc : L ⊆ spectralSetᶜ := by
    intro K hK
    exact (spectralGap_pos_iff K).mp ((Real.exp_pos _).trans_le hK)
  have he : {K | K ∉ spectralSet ∧ spectralExhaustion K ≤ r} =
      {K | K ∈ L ∧ spectralExhaustion K ≤ r} := by
    ext K
    constructor
    · rintro ⟨hK,hr⟩
      exact ⟨spectralExhaustion_gap_bound hK hr,hr⟩
    · rintro ⟨hK,hr⟩
      exact ⟨hLc hK,hr⟩
  rw [he]
  exact hL.isClosed_le (spectralExhaustion_continuousOn.mono hLc) continuousOn_const

theorem spectralExhaustion_norm_bound {K : Coupling} {r : ℝ}
    (hr : spectralExhaustion K ≤ r) : ‖K‖ ≤ |r|+1 := by
  have hb : 0 ≤ spectralBarrier K := le_max_left _ _
  have hr' : ‖K.1‖^2+‖K.2‖^2 ≤ r := by dsimp [spectralExhaustion] at hr; linarith
  rw [Prod.norm_def,max_le_iff]
  constructor <;> nlinarith [sq_nonneg ‖K.1‖,sq_nonneg ‖K.2‖,
    norm_nonneg K.1,norm_nonneg K.2,abs_nonneg r,le_abs_self r]

theorem spectralExhaustion_sublevel_isCompact (r : ℝ) :
    IsCompact {K | K ∉ spectralSet ∧ spectralExhaustion K ≤ r} := by
  apply (isCompact_closedBall (0 : Coupling) (|r|+1)).of_isClosed_subset
    (spectralExhaustion_sublevel_isClosed r)
  intro K hK
  rw [mem_closedBall,dist_zero_right]
  exact spectralExhaustion_norm_bound hK.2

theorem spectralExhaustion_component_sublevel_isCompact {D : Set Coupling}
    (ho : IsOpen D) (hs : D ⊆ spectralSetᶜ) (hb : frontier D ⊆ spectralSet) (r : ℝ) :
    IsCompact {K | K ∈ D ∧ spectralExhaustion K ≤ r} := by
  have he : {K | K ∈ D ∧ spectralExhaustion K ≤ r} =
      closure D ∩ {K | K ∉ spectralSet ∧ spectralExhaustion K ≤ r} := by
    ext K
    constructor
    · rintro ⟨hK,hr⟩
      exact ⟨subset_closure hK,hs hK,hr⟩
    · rintro ⟨hcl,hsp,hr⟩
      refine ⟨?_,hr⟩
      by_contra hn
      apply hsp
      apply hb
      rw [ho.frontier_eq]
      exact ⟨hcl,hn⟩
  rw [he,inter_comm]
  exact (spectralExhaustion_sublevel_isCompact r).inter_right isClosed_closure

theorem pseudoconvex_of_spectral_component {D : Set Coupling}
    (ho : IsOpen D) (hs : D ⊆ spectralSetᶜ) (hb : frontier D ⊆ spectralSet) :
    IsPseudoconvex D := by
  refine ⟨spectralExhaustion,⟨spectralExhaustion_continuousOn.mono hs,?_⟩,
    spectralExhaustion_component_sublevel_isCompact ho hs hb⟩
  intro K V R hD
  exact spectralExhaustion_isPlurisubharmonic.2 K V R (fun z hz => hs (hD z hz))

theorem highDomain_isPseudoconvex : IsPseudoconvex highDomain :=
  pseudoconvex_of_spectral_component highDomain_isOpen highDomain_subset_spectralComplement
    frontier_high_subset_spectralSet

theorem lowDomain_isPseudoconvex : IsPseudoconvex lowDomain :=
  pseudoconvex_of_spectral_component lowDomain_isOpen lowDomain_subset_spectralComplement
    frontier_low_subset_spectralSet

end
end IsingBulk.Joint
