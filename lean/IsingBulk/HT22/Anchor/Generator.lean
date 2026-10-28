import IsingBulk.HT22.Anchor.SourcePiola
import IsingBulk.HT22.Tail.PhysicalRecurrence
namespace IsingBulk.HT22.Anchor
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Geometry IsingBulk.HT22.Tail Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

/-- Full anchor scalar generator: the signed resolvent stays inside G. -/
def regularTransportStep {N : ℕ} (anchor : Fin N) (τ : ℝ) (p m : ℝ → ℝ)
    (F : ℂ → (Fin N → ℝ) → ℂ) (t : ℂ) (θ : Fin N → ℝ) : ℂ :=
  deriv (fun s => F s θ) t-
    (∑ i,angularField anchor τ p m t θ i*
      deriv (fun x : ℝ => F t (Function.update θ i x)) (θ i))+
    regularDivergence anchor τ p m t θ*F t θ

theorem regularTransportStep_eq {N : ℕ} (anchor : Fin N) (τ : ℝ) (p m : ℝ → ℝ)
    (F : ℂ → (Fin N → ℝ) → ℂ) (t : ℂ) (θ : Fin N → ℝ) :
    regularTransportStep anchor τ p m F t θ = deriv (fun s => F s θ) t-
    (∑ i,angularField anchor τ p m t θ i*
      deriv (fun x : ℝ => F t (Function.update θ i x)) (θ i))+
    regularDivergence anchor τ p m t θ*F t θ := rfl

theorem source_generator_factors_mixed {N : ℕ} (anchor : Fin N) (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ)))
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
 :
    (∀ i a, PreferredMixedSmoothOn (fun z => (preferredContourMatrix τ p m z.2)⁻¹ i a) Ω) ∧
    (∀ a, PreferredMixedSmoothOn (fun z => Tail.inverseV z.1 (sourceCoordinate τ p m z.1 z.2 a)) Ω) ∧
    (∀ a, PreferredMixedSmoothOn (fun z => Tail.inverseT z.1 (sourceCoordinate τ p m z.1 z.2 a)) Ω) ∧
    (∀ a, PreferredMixedSmoothOn (fun z => residualField anchor z.1 (sourceCoordinate τ p m z.1 z.2) a) Ω) := by
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
  refine ⟨?_,hjet Tail.inverseV (fun z hz a => inverseV_joint_analytic _ _ (framePoint_inverse_analytic (hpoint z hz) a)),
    hjet Tail.inverseT (fun z hz a => inverseT_joint_analytic _ _ (framePoint_inverse_analytic (hpoint z hz) a)),?_⟩
  · intro i a z hz
    have hh := preferredContourMatrix_inverse_contDiffAt τ p m hp hm z.2 (hpoint z hz).matrix
    exact ⟨(contDiffAt_pi.mp (contDiffAt_pi.mp hh i) a).comp z contDiffAt_snd,
      differentiableAt_const (𝕜 := ℂ) ((preferredContourMatrix τ p m z.2)⁻¹ i a)⟩
  · intro a
    apply analytic_pullback_mixed τ δ p m hp hm Ω hpoint
      (fun x => residualField anchor x.1 x.2 a)
    intro z hz
    exact analyticAt_pi_iff.mp (residualField_analyticAt anchor z.1 _
      (framePoint_inverse_analytic (hpoint z hz)) (source_inverseV_ne_zero (hpoint z hz) anchor)) a

/-- Actual angular field and actual regular divergence, for use in every
finite transport. No analytically continued cutoff appears. -/
theorem source_generator_mixed {N : ℕ} (anchor : Fin N) (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
 :
    (∀ i, PreferredMixedSmoothOn (fun z => angularField anchor τ p m z.1 z.2 i) Ω) ∧
    PreferredMixedSmoothOn (fun z => regularDivergence anchor τ p m z.1 z.2) Ω := by
  obtain ⟨hM,hv,hu,hB⟩ := source_generator_factors_mixed anchor τ δ p m hp hm Ω hpoint
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
theorem regularTransportStep_mixed {N : ℕ} (anchor : Fin N) (τ : ℝ) (p m : ℝ → ℝ)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hV : ∀ i, PreferredMixedSmoothOn (fun z => angularField anchor τ p m z.1 z.2 i) Ω)
    (hD : PreferredMixedSmoothOn (fun z => regularDivergence anchor τ p m z.1 z.2) Ω)
    (F : ℂ → (Fin N → ℝ) → ℂ)
    (hF : PreferredMixedSmoothOn (fun z => F z.1 z.2) Ω) :
    PreferredMixedSmoothOn (fun z => regularTransportStep anchor τ p m F z.1 z.2) Ω := by
  have hh := ((hF.parameter hΩ).sub (PreferredMixedSmoothOn.sum
    (fun i => (hV i).mul (hF.coordinate hΩ i)))).add (hD.mul hF)
  apply hh.congr hΩ
  intro z _
  exact (regularTransportStep_eq anchor τ p m F z.1 z.2).symm

/-- The literal physical derivative-minus-divergence step factors through
our anchor scalar generator. H=1: the full signed resolvent is differentiated
inside G, not improperly frozen by the anchor. -/
theorem physical_transport_factorization {N : ℕ} (anchor : Fin N)
    (τ δ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω,PreferredFramePoint τ δ p m z.1 z.2)
    (G : ℂ → (Fin N → ℝ) → ℂ)
    (hG : PreferredMixedSmoothOn (fun z => G z.1 z.2) Ω)
    (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    preferredTransportStep (angularField anchor τ p m)
      (fun t x => coordinateJacobian τ p m t x*G t x) s θ=
      coordinateJacobian τ p m s θ*regularTransportStep anchor τ p m G s θ := by
  have hJ := coordinateJacobian_mixed τ δ p m hp hm Ω hpoint (s,θ) hz
  have hV := (source_generator_mixed anchor τ δ p m hp hm Ω hΩ hpoint).1
  have hx {F : ℂ × (Fin N → ℝ) → ℂ} (hh : ContDiffAt ℝ ∞ F (s,θ)) (i : Fin N) :
      DifferentiableAt ℝ (fun x => F (s,Function.update θ i x)) (θ i) :=
    preferredMixed_coordinate_differentiable (fun t x => F (t,x)) s θ hh i
  have hh := preferredTransportStep_factored (angularField anchor τ p m)
    (coordinateJacobian τ p m) (fun _ _ => (1:ℂ)) G s θ (regularDivergence anchor τ p m s θ)
    hJ.2 (differentiableAt_const 1) (hG (s,θ) hz).2 (hx hJ.1)
    (fun _ => differentiableAt_const 1) (hx (hG (s,θ) hz).1)
    (fun i => hx (hV i (s,θ) hz).1 i)
    (coordinateJacobian_piola anchor τ δ p m hp hm Ω hΩ hpoint s θ hz)
    (by simp)
  simpa only [mul_one,regularTransportStep] using hh

end
end IsingBulk.HT22.Anchor
