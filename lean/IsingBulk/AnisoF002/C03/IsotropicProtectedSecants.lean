import IsingBulk.AnisoF002.C03.IsotropicJointSecants
import IsingBulk.AnisoF002.Isotropic.RightCovariance

/-!
# One protected neighborhood for the actual right secants

The neighborhood and lower bound are selected on the whole compact right
pair interval, before any particle number or derivative order.  The
objects are the actual first and second `dslope` functions and the ratio
used in the covariance field.  Every partial coincidence is included.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology
open Filter Set Metric

def rightPairParameterSegment (S : ℝ) : Set (ℂ × ℂ × ℂ) :=
  {(S : ℂ)} ×ˢ
    ((Complex.ofReal '' Icc (-rightBranchEndpoint S) (rightBranchEndpoint S)) ×ˢ
      (Complex.ofReal '' Icc (-rightBranchEndpoint S) (rightBranchEndpoint S)))

theorem rightPairParameterSegment_isCompact (S : ℝ) :
    IsCompact (rightPairParameterSegment S) :=
  isCompact_singleton.prod
    ((isCompact_Icc.image Complex.continuous_ofReal).prod
      (isCompact_Icc.image Complex.continuous_ofReal))

theorem rightPairParameterSegment_fst_mem {S : ℝ} {q : ℂ × ℂ × ℂ}
    (hq : q ∈ rightPairParameterSegment S) :
    (q.1, q.2.1) ∈ rightParameterSegment S := ⟨hq.1, hq.2.1⟩

theorem rightPairParameterSegment_snd_mem {S : ℝ} {q : ℂ × ℂ × ℂ}
    (hq : q ∈ rightPairParameterSegment S) :
    (q.1, q.2.2) ∈ rightParameterSegment S := ⟨hq.1, hq.2.2⟩

def jointSecantRatio (U : ℂ × ℂ → ℂ) (q : ℂ × ℂ × ℂ) : ℂ :=
  jointFirstSecant U q ^ 2 / jointSecondSecant U q

theorem jointSecantRatio_analyticAt (U : ℂ × ℂ → ℂ) (q : ℂ × ℂ × ℂ)
    (hfirst : AnalyticAt ℂ (jointFirstSecant U) q)
    (hsecond : AnalyticAt ℂ (jointSecondSecant U) q)
    (hne : jointSecondSecant U q ≠ 0) :
    AnalyticAt ℂ (jointSecantRatio U) q :=
  (hfirst.pow 2).div hsecond hne

/-- Joint analyticity of both genuine secants at every pair on the full
limiting right arc, including the full diagonal and both branch ends. -/
theorem rightPair_actual_secants_analytic (S : ℝ) (hS : 0 < S ∧ S < 2)
    (q : ℂ × ℂ × ℂ) (hq : q ∈ rightPairParameterSegment S) :
    AnalyticAt ℂ (jointFirstSecant explicitRightInverse) q ∧
      AnalyticAt ℂ (jointSecondSecant explicitRightInverse) q := by
  have ha := explicitRightInverse_data_on_segment S hS _
    (rightPairParameterSegment_fst_mem hq)
  have hb := explicitRightInverse_data_on_segment S hS _
    (rightPairParameterSegment_snd_mem hq)
  have hda := explicitRightInverse_dispersion_eventually (q.1, q.2.1) ha.2.1
  have hdb := explicitRightInverse_dispersion_eventually (q.1, q.2.2) hb.2.1
  exact ⟨jointFirstSecant_analyticAt explicitRightInverse q ha.1 hb.1 hda hdb ha.2.2.1,
    jointSecondSecant_analyticAt explicitRightInverse q ha.1 hb.1 hda hdb
      ha.2.2.1 hb.2.2.1⟩

/-- Protected joint secants and all fixed joint jets on one neighborhood
chosen before N. The complete variance is a separate, population-level
quantity, so it is not inferred from this two-coordinate statement. -/
theorem exists_right_secants_protected_neighborhood (S : ℝ) (hS : 0 < S ∧ S < 2) :
    ∃ r c : ℝ, 0 < r ∧ 0 < c ∧
      rightPairParameterSegment S ⊆ thickening r (rightPairParameterSegment S) ∧
      AnalyticOnNhd ℂ (jointFirstSecant explicitRightInverse)
        (cthickening r (rightPairParameterSegment S)) ∧
      AnalyticOnNhd ℂ (jointSecondSecant explicitRightInverse)
        (cthickening r (rightPairParameterSegment S)) ∧
      AnalyticOnNhd ℂ (jointSecantRatio explicitRightInverse)
        (cthickening r (rightPairParameterSegment S)) ∧
      (∀ q ∈ cthickening r (rightPairParameterSegment S),
        c ≤ (jointSecondSecant explicitRightInverse q).re) ∧
      ∀ k : ℕ, ∃ C₁ C₂ C₃ : ℝ,
        (∀ q ∈ cthickening r (rightPairParameterSegment S),
          ‖iteratedFDeriv ℂ k (jointFirstSecant explicitRightInverse) q‖ ≤ C₁) ∧
        (∀ q ∈ cthickening r (rightPairParameterSegment S),
          ‖iteratedFDeriv ℂ k (jointSecondSecant explicitRightInverse) q‖ ≤ C₂) ∧
        (∀ q ∈ cthickening r (rightPairParameterSegment S),
          ‖iteratedFDeriv ℂ k (jointSecantRatio explicitRightInverse) q‖ ≤ C₃) := by
  obtain ⟨r₀, c₀, _, hc₀, hsub₀, _, hsec₀, _⟩ :=
    exists_rightCovariance_common_domain S hS
  let c := c₀ / 2
  have hc : 0 < c := half_pos hc₀
  have hlower : ∀ q ∈ rightPairParameterSegment S,
      c < (jointSecondSecant explicitRightInverse q).re := by
    intro q hq
    have h := hsec₀ q.1 q.2.2
      (hsub₀ (rightPairParameterSegment_snd_mem hq)) q.2.1
      (hsub₀ (rightPairParameterSegment_fst_mem hq))
    change c₀ ≤ (jointSecondSecant explicitRightInverse q).re at h
    dsimp only [c]
    linarith
  let P : (ℂ × ℂ × ℂ) → Prop := fun q =>
    AnalyticAt ℂ (jointFirstSecant explicitRightInverse) q ∧
      AnalyticAt ℂ (jointSecondSecant explicitRightInverse) q ∧
      c < (jointSecondSecant explicitRightInverse q).re
  have hinside : rightPairParameterSegment S ⊆ interior {q | P q} := by
    intro q hq
    apply mem_interior_iff_mem_nhds.mpr
    have h := rightPair_actual_secants_analytic S hS q hq
    have hcq := Complex.continuous_re.continuousAt.comp h.2.continuousAt
    filter_upwards [h.1.eventually_analyticAt, h.2.eventually_analyticAt,
      hcq.eventually (lt_mem_nhds (hlower q hq))] with z h₁ h₂ h₃
    exact ⟨h₁, h₂, h₃⟩
  obtain ⟨r, hr, hsub⟩ := (rightPairParameterSegment_isCompact S).exists_cthickening_subset_open
    isOpen_interior hinside
  have hall : ∀ q ∈ cthickening r (rightPairParameterSegment S), P q :=
    fun q hq => (interior_subset (s := {q | P q})) (hsub hq)
  have hfirst : AnalyticOnNhd ℂ (jointFirstSecant explicitRightInverse)
      (cthickening r (rightPairParameterSegment S)) := fun q hq => (hall q hq).1
  have hsecond : AnalyticOnNhd ℂ (jointSecondSecant explicitRightInverse)
      (cthickening r (rightPairParameterSegment S)) := fun q hq => (hall q hq).2.1
  have hratio : AnalyticOnNhd ℂ (jointSecantRatio explicitRightInverse)
      (cthickening r (rightPairParameterSegment S)) := by
    intro q hq
    apply jointSecantRatio_analyticAt _ q (hfirst q hq) (hsecond q hq)
    intro hz
    have hpos := (hall q hq).2.2
    rw [hz, Complex.zero_re] at hpos
    linarith
  refine ⟨r, c, hr, hc, self_subset_thickening hr _, hfirst, hsecond, hratio,
    (fun q hq => (hall q hq).2.2.le), ?_⟩
  intro k
  obtain ⟨C₁, h₁⟩ := (rightPairParameterSegment_isCompact S).cthickening.exists_bound_of_continuousOn
    (hfirst.iteratedFDeriv k).continuousOn
  obtain ⟨C₂, h₂⟩ := (rightPairParameterSegment_isCompact S).cthickening.exists_bound_of_continuousOn
    (hsecond.iteratedFDeriv k).continuousOn
  obtain ⟨C₃, h₃⟩ := (rightPairParameterSegment_isCompact S).cthickening.exists_bound_of_continuousOn
    (hratio.iteratedFDeriv k).continuousOn
  exact ⟨C₁, C₂, C₃, h₁, h₂, h₃⟩

end IsingBulk.AnisoF002.Isotropic
