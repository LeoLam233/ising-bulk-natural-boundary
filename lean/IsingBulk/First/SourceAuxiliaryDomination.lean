import IsingBulk.First.SourceAuxiliaryRegularity
import IsingBulk.First.AuxiliaryDomination

/-! A genuine noncompact L1 majorant for the literal source auxiliary density
on a fixed-radius complex parameter neighborhood. Its constants are allowed
to depend on that radius and center; this is only a local differentiation tool. -/
namespace IsingBulk.First
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology BigOperators ContDiff

theorem sourceAngularExponent_joint_continuousAt {N : ℕ} (r : ℝ) (hr : r ≠ 0)
    (s : ℂ) (hs : s ≠ 0) (u : DoubleAngularVector N)
    (f : SingularFactorIndex N) (hf : validSourceFactor f) :
    ContinuousAt (fun q : ℂ × DoubleAngularVector N =>
      sourceAngularExponent r q.1 (fun _ => 1) (fun _ => 1) f q.2) (s,u) := by
  have hh := sourcePhaseSum_joint_contDiffAt (fun _ : Unit => f) (fun _ => hf)
    r s (fun _ => 1) u hr hs
  let g : ℂ × DoubleAngularVector N → ((ℝ × ℂ) × (Unit → ℝ)) × DoubleAngularVector N :=
    fun q => (((r,q.1),fun _ => 1),q.2)
  have hg : ContinuousAt g (s,u) := by dsimp [g]; fun_prop
  have hc := hh.continuousAt.comp (f := g) hg
  simpa only [g, Function.comp_def, sourcePhaseSum, Fintype.sum_unique, Complex.ofReal_one,
    one_mul] using hc

theorem sourceAuxiliaryDensity_local_dominator (N : ℕ) (hN : 0 < N) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (w : DoubleAngularVector N → ℝ)
    (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (J : Finset (SingularFactorIndex N)) (hJ : ∀ f ∈ J, validSourceFactor f)
    {s : ℂ} (hs : s ∈ dampingDomain r) :
    ∃ U : Set ℂ, IsOpen U ∧ s ∈ U ∧ U ⊆ dampingDomain r ∧
      ∃ b : DoubleAngularVector N × (J → ℝ) → ℝ,
        Integrable b (volume.prod (volume.restrict (positiveAuxiliaryOrthant J))) ∧
        ∀ᵐ p ∂volume.prod (volume.restrict (positiveAuxiliaryOrthant J)),
          ∀ t ∈ U, ‖sourceAuxiliaryDensity r w J t p‖ ≤ b p := by
  classical
  obtain ⟨ε,hε,hεD⟩ := Metric.mem_nhds_iff.mp (dampingDomain_mem_nhds hs)
  have hd : 0 < ε/2 := by linarith
  let C := closedBall s (ε/2)
  let U := ball s (ε/2)
  have hC : IsCompact C := isCompact_closedBall _ _
  have hCD : C ⊆ dampingDomain r := (closedBall_subset_ball (by linarith : ε/2 < ε)).trans hεD
  let A : ℂ → DoubleAngularVector N → ℂ := fun t u => localizedRegularAmplitude r t w J u
  let d : J → ℂ → DoubleAngularVector N → ℂ := fun i t u =>
    sourceAngularExponent r t (fun _ => 1) (fun _ => 1) i.1 u
  have hA : ContinuousOn (fun p : ℂ × DoubleAngularVector N => A p.1 p.2) (C ×ˢ tsupport w) := by
    intro p hp
    have hh := localizedRegularAmplitude_joint_contDiffAt w hw J r p.1 p.2 hr.ne' (hCD hp.1).1
      (fun f _ => sourceFactorDenominator_ne_zero_damped N hN hr hr1 (hCD hp.1) p.2 f)
    let g : ℂ × DoubleAngularVector N → (ℝ × ℂ) × DoubleAngularVector N := fun q => ((r,q.1),q.2)
    have hg : ContinuousAt g p := by dsimp [g]; fun_prop
    exact (hh.continuousAt.comp (f := g) hg).continuousWithinAt
  have hdcont (i : J) : ContinuousOn (fun p : ℂ × DoubleAngularVector N => d i p.1 p.2)
      (C ×ˢ tsupport w) := by
    intro p hp
    exact (sourceAngularExponent_joint_continuousAt r hr.ne' p.1 (hCD hp.1).1 p.2 i.1 (hJ i.1 i.2)).continuousWithinAt
  have hdneg (i : J) (t : ℂ) (ht : t ∈ C) (u : DoubleAngularVector N) (_hu : u ∈ tsupport w) :
      (d i t u).re < 0 :=
    singularFactorExponent_re_negative hN hr hr1 (hCD ht).2 _ _ (by simp) (by simp) u i.1 1
  have hAz (t : ℂ) (_ht : t ∈ C) (u : DoubleAngularVector N) (hu : u ∉ tsupport w) : A t u = 0 := by
    have hz : w u = 0 := by
      by_contra hn
      exact hu (subset_closure hn)
    simp only [A, localizedRegularAmplitude, hz, Complex.ofReal_zero, zero_mul]
  obtain ⟨b,hb,hbb⟩ := compact_parameter_auxiliary_dominator (μ := volume) hC hc A d hA hdcont hdneg hAz
  have horth : MeasurableSet (positiveAuxiliaryOrthant J) :=
    MeasurableSet.univ_pi (fun _ => measurableSet_Ioi)
  have hp : ∀ᵐ p : DoubleAngularVector N × (J → ℝ)
      ∂volume.prod (volume.restrict (positiveAuxiliaryOrthant J)), p.2 ∈ positiveAuxiliaryOrthant J := by
    apply (Measure.ae_prod_iff_ae_ae (horth.preimage measurable_snd)).mpr
    exact Filter.Eventually.of_forall (fun _ => ae_restrict_mem horth)
  refine ⟨U,isOpen_ball,mem_ball_self hd,(fun _ ht => hCD (ball_subset_closedBall ht)),b,hb,?_⟩
  filter_upwards [hp] with p hp
  intro t ht
  have hh := hbb t (ball_subset_closedBall ht) p hp
  simpa only [sourceAuxiliaryDensity, sourcePhaseSum, A, d, mul_comm] using hh

end
end IsingBulk.First
