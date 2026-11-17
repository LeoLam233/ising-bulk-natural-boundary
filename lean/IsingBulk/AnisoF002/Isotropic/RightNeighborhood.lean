import IsingBulk.AnisoF002.Isotropic.ExplicitRightInverse
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.Compact

/-!
# A common convex complex right-inverse neighborhood

This supplies the right-domain part of frozen F002 Lemma 7.3 using the
single explicit inverse from `ExplicitRightInverse`.  One neighborhood
works for the whole real right interval and for all fixed joint derivative
orders.  The actual second derivative has a uniform positive real part.

The remaining left-arc extension and the inclusion of every actual
population-dependent deformed image are not asserted here.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology
open Filter Set Metric

def explicitRightDenominator (q : ℂ × ℂ) : ℂ :=
  Complex.sin (q.2 - explicitRightInverse q) - Complex.sin (explicitRightInverse q)

def explicitRightCurvature (q : ℂ × ℂ) : ℂ :=
  inverseCurvature q.1 (explicitRightInverse q) (q.2 - explicitRightInverse q)

/-- The full fixed-parameter real right interval in the joint parameter space. -/
def rightParameterSegment (S : ℝ) : Set (ℂ × ℂ) :=
  {(S : ℂ)} ×ˢ (Complex.ofReal '' Icc (-rightBranchEndpoint S) (rightBranchEndpoint S))

theorem explicitRightDenominator_analyticAt (q : ℂ × ℂ)
    (hU : AnalyticAt ℂ explicitRightInverse q) :
    AnalyticAt ℂ explicitRightDenominator q := by
  exact (Complex.analyticAt_sin.comp (analyticAt_snd.sub hU)).sub
    (Complex.analyticAt_sin.comp hU)

theorem explicitRightCurvature_analyticAt (q : ℂ × ℂ)
    (hU : AnalyticAt ℂ explicitRightInverse q) (hD : explicitRightDenominator q ≠ 0) :
    AnalyticAt ℂ explicitRightCurvature q :=
  joint_inverseCurvature_analyticAt explicitRightInverse q hU hD

theorem explicitRightInverse_dispersion_eventually (q : ℂ × ℂ)
    (hc : Complex.cos (q.2 / 2) ≠ 0) :
    ∀ᶠ z in 𝓝 q,
      Complex.cos (explicitRightInverse z) +
        Complex.cos (z.2 - explicitRightInverse z) = z.1 := by
  have hcont : ContinuousAt (fun z : ℂ × ℂ => Complex.cos (z.2 / 2)) q :=
    Complex.continuous_cos.continuousAt.comp
      (continuousAt_snd.div continuousAt_const (by norm_num))
  filter_upwards [hcont.eventually_ne hc] with z hz
  exact explicitRightInverse_dispersion z hz

theorem explicitRightInverse_second_derivative (q : ℂ × ℂ)
    (hU : AnalyticAt ℂ explicitRightInverse q)
    (hc : Complex.cos (q.2 / 2) ≠ 0) (hD : explicitRightDenominator q ≠ 0) :
    HasDerivAt (deriv (fun z => explicitRightInverse (q.1, z)))
      (explicitRightCurvature q) q.2 :=
  joint_inverse_coordinate_second_derivative explicitRightInverse q.1 q.2 hU
    (explicitRightInverse_dispersion_eventually q hc) hD

theorem explicitRightInverse_data_on_arc (S w : ℝ) (hS : 0 < S ∧ S < 2)
    (hw : w ∈ Icc (-rightBranchEndpoint S) 0) :
    AnalyticAt ℂ explicitRightInverse ((S : ℂ), (rightArcCoordinate S w : ℂ)) ∧
      Complex.cos ((rightArcCoordinate S w : ℂ) / 2) ≠ 0 ∧
      explicitRightDenominator ((S : ℂ), (rightArcCoordinate S w : ℂ)) ≠ 0 ∧
      0 < (explicitRightCurvature ((S : ℂ), (rightArcCoordinate S w : ℂ))).re := by
  have hv := rightArcCoordinate_inside_discriminant_interval S w hS hw
  have hb := rightInverseRatio_bounds S (rightArcCoordinate S w) hS hv
  have hu := explicitRightInverse_on_right_arc S w hS hw
  have hφ : (rightArcCoordinate S w : ℂ) - (w : ℂ) = (rightArcPhase S w : ℂ) := by
    unfold rightArcCoordinate
    push_cast
    ring
  have hDreal := rightArc_inverse_denominator_pos S w hS hw
  have hDval : explicitRightDenominator ((S : ℂ), (rightArcCoordinate S w : ℂ)) =
      ((Real.sin (rightArcPhase S w) - Real.sin w : ℝ) : ℂ) := by
    unfold explicitRightDenominator
    rw [hu, hφ]
    simp only [Complex.ofReal_sub, Complex.ofReal_sin]
  have hKval : explicitRightCurvature ((S : ℂ), (rightArcCoordinate S w : ℂ)) =
      ((S * (1 - Real.cos w * Real.cos (rightArcPhase S w)) /
        (Real.sin (rightArcPhase S w) - Real.sin w) ^ 3 : ℝ) : ℂ) := by
    unfold explicitRightCurvature inverseCurvature
    rw [hu, hφ]
    simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_sub,
      Complex.ofReal_one, Complex.ofReal_pow, Complex.ofReal_sin, Complex.ofReal_cos]
  refine ⟨explicitRightInverse_analyticAt_real S (rightArcCoordinate S w) hS hv, ?_, ?_, ?_⟩
  · have hcR : (Real.cos (rightArcCoordinate S w / 2) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt hb.1)
    simpa using hcR
  · rw [hDval]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt hDreal)
  · rw [hKval, Complex.ofReal_re]
    exact real_inverse_curvature_pos S w (rightArcPhase S w) hS.1 hDreal

theorem rightParameterSegment_isCompact (S : ℝ) : IsCompact (rightParameterSegment S) :=
  isCompact_singleton.prod (isCompact_Icc.image Complex.continuous_ofReal)

theorem rightParameterSegment_nonempty (S : ℝ) : (rightParameterSegment S).Nonempty := by
  have hb : 0 ≤ rightBranchEndpoint S := Real.arccos_nonneg (S - 1)
  refine ⟨((S : ℂ), 0), ?_⟩
  exact ⟨rfl, 0, ⟨by linarith, hb⟩, by simp⟩

theorem rightParameterSegment_convex (S : ℝ) : Convex ℝ (rightParameterSegment S) := by
  exact (convex_singleton (S : ℂ)).prod
    ((convex_Icc (-rightBranchEndpoint S) (rightBranchEndpoint S)).linear_image
      Complex.ofRealCLM.toLinearMap)

theorem explicitRightInverse_data_on_segment (S : ℝ) (hS : 0 < S ∧ S < 2)
    (q : ℂ × ℂ) (hq : q ∈ rightParameterSegment S) :
    AnalyticAt ℂ explicitRightInverse q ∧ Complex.cos (q.2 / 2) ≠ 0 ∧
      explicitRightDenominator q ≠ 0 ∧ 0 < (explicitRightCurvature q).re := by
  rcases q with ⟨s, z⟩
  rcases hq with ⟨hs, ⟨v, hv, hz⟩⟩
  change s = (S : ℂ) at hs
  subst s
  change (v : ℂ) = z at hz
  subst z
  have hv' : v ∈ rightArcCoordinate S '' Icc (-rightBranchEndpoint S) 0 := by
    rw [rightArcCoordinate_image S hS]
    exact hv
  rcases hv' with ⟨w, hw, rfl⟩
  exact explicitRightInverse_data_on_arc S w hS hw

/-- A single convex joint complex neighborhood works for the whole right
interval.  Its genuine second coordinate derivative has uniformly positive
real part, and every fixed joint Fréchet jet is bounded on the same protected
closed neighborhood. -/
theorem exists_right_inverse_common_convex_neighborhood (S : ℝ) (hS : 0 < S ∧ S < 2) :
    ∃ (r c : ℝ), 0 < r ∧ 0 < c ∧
      Convex ℝ (thickening r (rightParameterSegment S)) ∧
      rightParameterSegment S ⊆ thickening r (rightParameterSegment S) ∧
      AnalyticOnNhd ℂ explicitRightInverse (cthickening r (rightParameterSegment S)) ∧
      (∀ q ∈ cthickening r (rightParameterSegment S),
        Complex.cos (explicitRightInverse q) +
            Complex.cos (q.2 - explicitRightInverse q) = q.1 ∧
          explicitRightDenominator q ≠ 0 ∧
          HasDerivAt (deriv (fun z => explicitRightInverse (q.1, z)))
            (explicitRightCurvature q) q.2 ∧
          c ≤ (explicitRightCurvature q).re) ∧
      ∀ k : ℕ, ∃ C : ℝ, ∀ q ∈ cthickening r (rightParameterSegment S),
        ‖iteratedFDeriv ℂ k explicitRightInverse q‖ ≤ C := by
  have hcont : ContinuousOn (fun q => (explicitRightCurvature q).re) (rightParameterSegment S) := by
    intro q hq
    have hd := explicitRightInverse_data_on_segment S hS q hq
    exact (Complex.continuous_re.continuousAt.comp
      (explicitRightCurvature_analyticAt q hd.1 hd.2.2.1).continuousAt).continuousWithinAt
  obtain ⟨q₀, hq₀, hmin⟩ := (rightParameterSegment_isCompact S).exists_isMinOn
    (rightParameterSegment_nonempty S) hcont
  have hzero := (explicitRightInverse_data_on_segment S hS q₀ hq₀).2.2.2
  let c : ℝ := (explicitRightCurvature q₀).re / 2
  have hcpos : 0 < c := half_pos hzero
  have hclt : ∀ q ∈ rightParameterSegment S, c < (explicitRightCurvature q).re := by
    intro q hq
    have hle := hmin hq
    change (explicitRightCurvature q₀).re ≤ (explicitRightCurvature q).re at hle
    dsimp only [c]
    linarith
  let P : (ℂ × ℂ) → Prop := fun q =>
    AnalyticAt ℂ explicitRightInverse q ∧ Complex.cos (q.2 / 2) ≠ 0 ∧
      explicitRightDenominator q ≠ 0 ∧ c < (explicitRightCurvature q).re
  have hinside : rightParameterSegment S ⊆ interior {q | P q} := by
    intro q hq
    apply mem_interior_iff_mem_nhds.mpr
    have hd := explicitRightInverse_data_on_segment S hS q hq
    have hcos : ContinuousAt (fun z : ℂ × ℂ => Complex.cos (z.2 / 2)) q :=
      Complex.continuous_cos.continuousAt.comp
        (continuousAt_snd.div continuousAt_const (by norm_num))
    have hD := (explicitRightDenominator_analyticAt q hd.1).continuousAt
    have hK := (explicitRightCurvature_analyticAt q hd.1 hd.2.2.1).continuousAt
    filter_upwards [hd.1.eventually_analyticAt, hcos.eventually_ne hd.2.1,
      hD.eventually_ne hd.2.2.1,
      (Complex.continuous_re.continuousAt.comp hK).eventually (lt_mem_nhds (hclt q hq))]
      with z hUz hcz hDz hKz
    exact ⟨hUz, hcz, hDz, hKz⟩
  obtain ⟨r, hr, hsub⟩ := (rightParameterSegment_isCompact S).exists_cthickening_subset_open
    isOpen_interior hinside
  have hall : ∀ q ∈ cthickening r (rightParameterSegment S), P q :=
    fun q hq => (interior_subset (s := {q | P q})) (hsub hq)
  have hU : AnalyticOnNhd ℂ explicitRightInverse (cthickening r (rightParameterSegment S)) :=
    fun q hq => (hall q hq).1
  refine ⟨r, c, hr, hcpos, (rightParameterSegment_convex S).thickening r,
    self_subset_thickening hr _, hU, ?_, ?_⟩
  · intro q hq
    have hd := hall q hq
    exact ⟨explicitRightInverse_dispersion q hd.2.1, hd.2.2.1,
      explicitRightInverse_second_derivative q hd.1 hd.2.1 hd.2.2.1, hd.2.2.2.le⟩
  · intro k
    exact (rightParameterSegment_isCompact S).cthickening.exists_bound_of_continuousOn
      (hU.iteratedFDeriv k).continuousOn

end IsingBulk.AnisoF002.Isotropic
