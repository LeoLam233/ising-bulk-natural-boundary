import IsingBulk.HT22.Tail.SourceKernelCalculus
import IsingBulk.HT22.Tail.SeedCalculus

/-! # Mixed regularity of the actual fixed-v generator

Only primitive physical branch geometry and the actual nonzero mixed
covariance are assumed. No smoothness premise for any recursively formed
coefficient is used.
-/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Geometry Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

theorem sourceCoordinate_contDiffAt {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) (t : ℂ) (θ : Fin N → ℝ)
    (hSi : 0<(temperatureTrace t).im)
    (hW : ∀ i, 0<(temperatureTrace t-Complex.cos (deformedAngles τ p m θ i)).im) :
    ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) => sourceCoordinate τ p m z.1 z.2) (t,θ) := by
  have hq := preferredSourceCoordinate_contDiffAt τ p m hp hm t θ hSi hW
  have hb : ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) => preferredMovingBranch z.1) (t,θ) :=
    ContDiffAt.comp (f := fun z : ℂ × (Fin N → ℝ) => z.1)
      (g := preferredMovingBranch) (t,θ)
      ((preferredMovingBranch_analyticAt_upper t hSi).contDiffAt.restrict_scalars ℝ)
      contDiffAt_fst
  have he : (fun z : ℂ × (Fin N → ℝ) => sourceCoordinate τ p m z.1 z.2)=
      (fun z i => preferredSourceCoordinate τ p m z.1 z.2 i+preferredMovingBranch z.1) := by
    funext z i
    exact (sub_eq_iff_eq_add.mp (sourceCoordinate_moving_adapter τ p m z.1 z.2 i))
  rw [he]
  exact contDiffAt_pi.mpr (fun i => (contDiffAt_pi.mp hq i).add hb)

/-- An arbitrary analytic regular-coordinate scalar pulls back smoothly in
all real angles and holomorphically in the physical parameter. -/
theorem analytic_pullback_mixed {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ)))
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (F : ℂ × (Fin N → ℂ) → ℂ)
    (hF : ∀ z∈Ω, AnalyticAt ℂ F (z.1,sourceCoordinate τ p m z.1 z.2)) :
    PreferredMixedSmoothOn (fun z => F (z.1,sourceCoordinate τ p m z.1 z.2)) Ω := by
  intro z hz
  have h := hpoint z hz
  have hχR := sourceCoordinate_contDiffAt τ p m hp hm z.1 z.2 h.trace_im h.upper
  have ht : z.1≠0 := by intro he; have hh:=h.trace_im; simp [he,temperatureTrace] at hh
  have hχC := sourceCoordinate_parameter_analyticAt τ p m z.1 z.2 ht h.upper
  constructor
  · exact ContDiffAt.comp
      (f := fun z : ℂ × (Fin N → ℝ) => (z.1,sourceCoordinate τ p m z.1 z.2))
      (g := F) z ((hF z hz).contDiffAt.restrict_scalars ℝ) (contDiffAt_fst.prodMk hχR)
  · exact DifferentiableAt.comp
      (f := fun s : ℂ => (s,sourceCoordinate τ p m s z.2)) (g := F)
      z.1 (hF z hz).differentiableAt (differentiableAt_id.prodMk hχC.differentiableAt)

theorem framePoint_inverse_analytic {N : ℕ} {τ δ : ℝ} {p m : ℝ → ℝ}
    {t : ℂ} {θ : Fin N → ℝ} (h : PreferredFramePoint τ δ p m t θ) (i : Fin N) :
    AnalyticAt ℂ (fun z : ℂ × ℂ => regularInverse z.1 z.2)
      (t,sourceCoordinate τ p m t θ i) :=
  global_one_sided_joint_analytic t (deformedAngles τ p m θ i) δ
    h.delta_pos h.delta_lt h.trace_re h.trace_cap
    (by simpa only [deformedAngles_re] using (h.angles i).1)
    (by simpa only [deformedAngles_re] using (h.angles i).2) (h.upper i)

/-- All finite source factors required by the new scalar generator. -/
theorem source_generator_factors_mixed {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ)))
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hR : ∀ z∈Ω, sourceCovariance z.1 (sourceCoordinate τ p m z.1 z.2)≠0) :
    (∀ i a, PreferredMixedSmoothOn (fun z => (preferredContourMatrix τ p m z.2)⁻¹ i a) Ω) ∧
    (∀ a, PreferredMixedSmoothOn (fun z => inverseV z.1 (sourceCoordinate τ p m z.1 z.2 a)) Ω) ∧
    (∀ a, PreferredMixedSmoothOn (fun z => inverseT z.1 (sourceCoordinate τ p m z.1 z.2 a)) Ω) ∧
    (∀ a, PreferredMixedSmoothOn (fun z => residualField z.1 (sourceCoordinate τ p m z.1 z.2) a) Ω) := by
  have hjet (F : ℂ → ℂ → ℂ)
      (hF : ∀ z∈Ω, ∀ a, AnalyticAt ℂ (fun x : ℂ × ℂ => F x.1 x.2)
        (z.1,sourceCoordinate τ p m z.1 z.2 a)) (a : Fin N) :
      PreferredMixedSmoothOn (fun z => F z.1 (sourceCoordinate τ p m z.1 z.2 a)) Ω := by
    apply analytic_pullback_mixed τ δ p m hp hm Ω hpoint (fun x => F x.1 (x.2 a))
    intro z hz
    have hcoord : AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) => x.2 a)
        (z.1,sourceCoordinate τ p m z.1 z.2) :=
      (((ContinuousLinearMap.proj a : (Fin N → ℂ) →L[ℂ] ℂ).comp
        (ContinuousLinearMap.snd ℂ ℂ (Fin N → ℂ))).analyticAt _)
    exact AnalyticAt.comp (f := fun x : ℂ × (Fin N → ℂ) => (x.1,x.2 a))
      (g := fun x : ℂ × ℂ => F x.1 x.2) (hF z hz a) (analyticAt_fst.prod hcoord)
  refine ⟨?_,hjet inverseV (fun z hz a => inverseV_joint_analytic _ _ (framePoint_inverse_analytic (hpoint z hz) a)),
    hjet inverseT (fun z hz a => inverseT_joint_analytic _ _ (framePoint_inverse_analytic (hpoint z hz) a)),?_⟩
  · intro i a z hz
    have hh := preferredContourMatrix_inverse_contDiffAt τ p m hp hm z.2 (hpoint z hz).matrix
    exact ⟨(contDiffAt_pi.mp (contDiffAt_pi.mp hh i) a).comp z contDiffAt_snd,
      differentiableAt_const (𝕜 := ℂ) ((preferredContourMatrix τ p m z.2)⁻¹ i a)⟩
  · intro a
    apply analytic_pullback_mixed τ δ p m hp hm Ω hpoint
      (fun x => sourceResidual x.1 x.2 a)
    intro z hz
    exact analyticAt_pi_iff.mp (sourceResidual_analyticAt z.1 _
      (framePoint_inverse_analytic (hpoint z hz)) (hR z hz)) a

/-- Actual angular field and actual regular divergence, for use in every
finite transport. No analytically continued cutoff appears. -/
theorem source_generator_mixed {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hR : ∀ z∈Ω, sourceCovariance z.1 (sourceCoordinate τ p m z.1 z.2)≠0) :
    (∀ i, PreferredMixedSmoothOn (fun z => angularField τ p m z.1 z.2 i) Ω) ∧
    PreferredMixedSmoothOn (fun z => regularDivergence τ p m z.1 z.2) Ω := by
  obtain ⟨hM,hv,hu,hB⟩ := source_generator_factors_mixed τ δ p m hp hm Ω hpoint hR
  constructor
  · intro i
    have hh := (PreferredMixedSmoothOn.const Ω (-1)).mul
      (PreferredMixedSmoothOn.sum (fun a => (hM i a).mul ((hu a).add ((hv a).mul (hB a)))))
    apply hh.congr hΩ
    intro z _
    simp only [angularField,preferredAngularRepresentative,Matrix.mulVec,dotProduct,neg_one_mul]
  · exact PreferredMixedSmoothOn.sum (fun a =>
      PreferredMixedSmoothOn.sum (fun i => ((hM i a).mul (hv a)).mul ((hB a).coordinate hΩ i)))

/-- Mixed smoothness propagates under the actual HT22 scalar generator. -/
theorem regularTransportStep_mixed {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hV : ∀ i, PreferredMixedSmoothOn (fun z => angularField τ p m z.1 z.2 i) Ω)
    (hD : PreferredMixedSmoothOn (fun z => regularDivergence τ p m z.1 z.2) Ω)
    (F : ℂ → (Fin N → ℝ) → ℂ)
    (hF : PreferredMixedSmoothOn (fun z => F z.1 z.2) Ω) :
    PreferredMixedSmoothOn (fun z => regularTransportStep τ p m F z.1 z.2) Ω := by
  have hh := ((hF.parameter hΩ).sub (PreferredMixedSmoothOn.sum
    (fun i => (hV i).mul (hF.coordinate hΩ i)))).add (hD.mul hF)
  apply hh.congr hΩ
  intro z _
  exact (regularTransportStep_eq τ p m F z.1 z.2).symm

end
end IsingBulk.HT22.Tail
