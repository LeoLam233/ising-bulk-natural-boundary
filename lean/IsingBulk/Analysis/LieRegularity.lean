import IsingBulk.Analysis.LieGeometry
import IsingBulk.Analysis.LieLocal

/-! Explicit admissibility for the source's analytic operations. Smoothness
on the regular locus is separate from integrability and a local majorant.
No boundary-flux or derivative-of-integral identity is a regularity field. -/
namespace IsingBulk.Lie
noncomputable section
open Set MeasureTheory Filter
open scoped Topology

/-- A finite stage needs only these consequences of smoothness, together with
integrability and local domination on the punctured domain. -/
structure StageRegularity {n : ℕ} (T : PuncturedTorus n) (U : Set ℂ)
    (V : ℂ → AngularSpace n → Fin (n+1) → ℂ)
    (A : ℂ → AngularSpace n → ℂ) : Prop where
  parameter : ∀ s ∈ U, ∀ x ∈ T.regular, DifferentiableAt ℂ (fun t => A t x) s
  spatial : ∀ s ∈ U, ∀ x ∈ T.regular, DifferentiableAt ℝ (A s) x
  derivative_continuous : ∀ s ∈ U,
    ContinuousOn (fun x => deriv (fun t => A t x) s) T.regular
  integrable : ∀ s ∈ U, Integrable (A s) T.measure
  divergence_integrable : ∀ s ∈ U,
    Integrable (divergence (fun x i => V s x i * A s x)) T.measure
  majorant : ∀ s ∈ U, ∃ W ∈ 𝓝 s, W ⊆ U ∧ ∃ b : AngularSpace n → ℝ,
    Integrable b T.measure ∧
    ∀ x ∈ T.regular, ∀ t ∈ W, ‖deriv (fun r => A r x) t‖ ≤ b x

def StageRegularity.differentiationData {n : ℕ} {T : PuncturedTorus n} {U : Set ℂ}
    {V : ℂ → AngularSpace n → Fin (n+1) → ℂ} {A : ℂ → AngularSpace n → ℂ}
    (h : StageRegularity T U V A) (hU : IsOpen U) {s : ℂ} (hs : s ∈ U) :
    DifferentiationData T.measure A s := by
  apply Classical.choice
  obtain ⟨W, hW, hWU, b, hb, hbound⟩ := h.majorant s hs
  refine ⟨⟨W, hW, b, ?_, h.integrable s hs, ?_, ?_, hb, ?_⟩⟩
  · filter_upwards [hU.mem_nhds hs] with t ht
    have hc : ContinuousOn (A t) T.regular :=
      fun x hx => (h.spatial t ht x hx).continuousAt.continuousWithinAt
    exact (hc.mono inter_subset_right).aestronglyMeasurable T.domain_measurable
  · exact (h.derivative_continuous s hs).mono inter_subset_right
      |>.aestronglyMeasurable T.domain_measurable
  · filter_upwards [ae_restrict_mem T.domain_measurable] with x hx
    exact hbound x hx.2
  · filter_upwards [ae_restrict_mem T.domain_measurable] with x hx
    exact fun t ht => h.parameter t (hWU ht) x hx.2

/-- Genuine Stokes data for a regular stage, obtained from the geometric
torus and the actual regularity of the field and density. -/
def StageRegularity.fluxExhaustion {n : ℕ} {T : PuncturedTorus n} {U : Set ℂ}
    {V : ℂ → AngularSpace n → Fin (n+1) → ℂ} {A : ℂ → AngularSpace n → ℂ}
    (h : StageRegularity T U V A)
    (hV : ∀ s ∈ U, ∀ x ∈ T.regular, ∀ i, DifferentiableAt ℝ (fun y => V s y i) x)
    {s : ℂ} (hs : s ∈ U)
    (hp : ∀ i x, V s (i.insertNth (T.upper i) x) i * A s (i.insertNth (T.upper i) x) =
      V s (i.insertNth (T.lower i) x) i * A s (i.insertNth (T.lower i) x))
    (hf : T.VanishingFlux (fun x i => V s x i * A s x)) :
    FluxExhaustion T.measure (fun x i => V s x i * A s x) :=
  T.toFluxExhaustion _
    (fun i x hx => ((hV s hs x hx i).mul (h.spatial s hs x hx)).continuousAt.continuousWithinAt)
    (fun x hx i => (hV s hs x hx i).mul (h.spatial s hs x hx))
    (h.divergence_integrable s hs) hp hf

theorem StageRegularity.first_stage {n : ℕ} {T : PuncturedTorus n} {U : Set ℂ}
    {V : ℂ → AngularSpace n → Fin (n+1) → ℂ} {A : ℂ → AngularSpace n → ℂ}
    (h : StageRegularity T U V A) (hU : IsOpen U)
    (hV : ∀ s ∈ U, ∀ x ∈ T.regular, ∀ i, DifferentiableAt ℝ (fun y => V s y i) x)
    {s : ℂ} (hs : s ∈ U)
    (hp : ∀ i x, V s (i.insertNth (T.upper i) x) i * A s (i.insertNth (T.upper i) x) =
      V s (i.insertNth (T.lower i) x) i * A s (i.insertNth (T.lower i) x))
    (hf : T.VanishingFlux (fun x i => V s x i * A s x)) :
    HasDerivAt (fun t => ∫ x, A t x ∂T.measure) (∫ x, lieStep V A s x ∂T.measure) s :=
  first_stage_excision _ V A s (h.differentiationData hU hs)
    (h.fluxExhaustion hV hs hp hf) (h.divergence_integrable s hs)

theorem StageRegularity.lieStep_integrable {n : ℕ} {T : PuncturedTorus n} {U : Set ℂ}
    {V : ℂ → AngularSpace n → Fin (n+1) → ℂ} {A : ℂ → AngularSpace n → ℂ}
    (h : StageRegularity T U V A) (hU : IsOpen U) {s : ℂ} (hs : s ∈ U) :
    Integrable (lieStep V A s) T.measure := by
  let d := h.differentiationData hU hs
  have hi := (hasDerivAt_integral_of_dominated_loc_of_deriv_le d.mem_nhds d.measurable
    d.integrable d.derivative_measurable d.derivative_bound d.bound_integrable
    (d.differentiable.mono fun x hx t ht => (hx t ht).hasDerivAt)).1
  exact hi.sub (h.divergence_integrable s hs)

end
end IsingBulk.Lie
