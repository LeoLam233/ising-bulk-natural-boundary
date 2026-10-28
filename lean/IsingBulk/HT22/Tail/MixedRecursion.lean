import IsingBulk.HT22.Tail.MarkedRecursion
import IsingBulk.HT22.Tail.SourceMixedCalculus

/-! # Primitive source geometry closes every finite marked recursion

The old transport/field/kernel are not invoked: only generic mixed-calculus
closure is reused. Actual finite base regularity is established from the
one-sided physical chart and nonzero new mixed covariance.
-/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 Filter
open scoped BigOperators ContDiff Matrix.Norms.Elementwise Topology
set_option backward.isDefEq.respectTransparency false

theorem sourceOrdinaryKernel_mixed {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ)))
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (a : Fin N × Fin N) :
    PreferredMixedSmoothOn (fun z => sourceOrdinaryKernel τ p m z.1 z.2 a.1 a.2) Ω := by
  apply analytic_pullback_mixed τ δ p m hp hm Ω hpoint
    (fun z => regularOrdinaryKernel z.1 z.2 a.1 a.2)
  intro z hz
  have h := hpoint z hz
  exact analyticAt_pi_iff.mp (analyticAt_pi_iff.mp
    (source_regularOrdinaryKernel_analyticAt τ δ p m z.1 z.2
      h.delta_pos h.delta_lt h.trace_re h.trace_cap h.angles h.upper) a.1) a.2

/-- Actual kernel-entry material derivatives inherit mixed regularity from
finitely many entry and angular-field functions. -/
theorem ordinaryMaterialEntry_mixed {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hV : ∀ i, PreferredMixedSmoothOn
      (fun z => angularField τ p m z.1 z.2 i) Ω)
    (hK : ∀ a : Fin N × Fin N, PreferredMixedSmoothOn
      (fun z => sourceOrdinaryKernel τ p m z.1 z.2 a.1 a.2) Ω)
    (a : Fin N × Fin N) :
    PreferredMixedSmoothOn (fun z => ordinaryMaterialEntry τ p m z.1 z.2 a) Ω := by
  have hh := ((hK a).parameter hΩ).sub (PreferredMixedSmoothOn.sum
    (fun i => (hV i).mul ((hK a).coordinate hΩ i)))
  apply hh.congr hΩ
  intro z hz
  have hs : DifferentiableAt ℂ (fun t => sourceOrdinaryKernel τ p m t z.2) z.1 := by
    apply differentiableAt_pi.mpr
    intro i
    apply differentiableAt_pi.mpr
    intro j
    exact (hK (i,j) z hz).2
  have hθ (k : Fin N) : DifferentiableAt ℝ
      (fun x => sourceOrdinaryKernel τ p m z.1 (Function.update z.2 k x)) (z.2 k) := by
    apply differentiableAt_pi.mpr
    intro i
    apply differentiableAt_pi.mpr
    intro j
    have hx := (hK (i,j) z hz).1.differentiableAt (by simp)
    have hg := (hasDerivAt_const (z.2 k) z.1).prodMk (hasDerivAt_update z.2 k (z.2 k))
    exact (hx.hasFDerivAt.comp_hasDerivAt_of_eq (z.2 k) hg
      (by simp only [Function.update_eq_self,Prod.mk.eta])).differentiableAt
  have hsd := hs.hasDerivAt
  have hsd' := hasDerivAt_pi.mp (hasDerivAt_pi.mp hsd a.1) a.2
  have hθd (k : Fin N) :=
    hasDerivAt_pi.mp (hasDerivAt_pi.mp (hθ k).hasDerivAt a.1) a.2
  unfold ordinaryMaterialEntry
  rw [hsd'.deriv]
  simp_rw [(hθd _).deriv]

/-- Only these finitely many base source functions need mixed regularity.
There is no assumption on any generated coefficient or on its norm. -/
def MarkedBaseSmoothness {N : ℕ} (τ : ℝ) (η p m r : ℝ → ℝ)
    (Ω : Set (ℂ × (Fin N → ℝ))) : Prop :=
  (∀ i, PreferredMixedSmoothOn (fun z => angularField τ p m z.1 z.2 i) Ω) ∧
  PreferredMixedSmoothOn (fun z => regularDivergence τ p m z.1 z.2) Ω ∧
  (∀ a : Fin N × Fin N, PreferredMixedSmoothOn
    (fun z => sourceOrdinaryKernel τ p m z.1 z.2 a.1 a.2) Ω) ∧
  PreferredMixedSmoothOn (fun z => regularSeedCoefficient τ η p m r z.1 z.2) Ω

theorem wordCoefficient_mixed {N : ℕ} (τ : ℝ) (η p m r : ℝ → ℝ)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hb : MarkedBaseSmoothness τ η p m r Ω)
    (j : ℕ) (w : MarkedWord N j) :
    PreferredMixedSmoothOn (fun z => wordCoefficient τ η p m r j w z.1 z.2) Ω := by
  induction j with
  | zero => exact hb.2.2.2
  | succ j ih =>
    cases hw : w 0 with
    | none =>
      simpa only [wordCoefficient,hw] using
        regularTransportStep_mixed τ p m Ω hΩ hb.1 hb.2.1
          (wordCoefficient τ η p m r j (Fin.tail w)) (ih (Fin.tail w))
    | some a =>
      simpa only [wordCoefficient,hw] using
        (ih (Fin.tail w)).mul (ordinaryMaterialEntry_mixed τ p m Ω hΩ hb.1 hb.2.2.1 a)

theorem wordDifferentiability_of_base {N : ℕ} (τ : ℝ) (η p m r : ℝ → ℝ)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hb : MarkedBaseSmoothness τ η p m r Ω) :
    WordDifferentiability τ η p m r Ω := by
  intro z hz
  have hcoord {F : ℂ × (Fin N → ℝ) → ℂ} (hF : PreferredMixedSmoothOn F Ω) (i : Fin N) :
      DifferentiableAt ℝ (fun x => F (z.1,Function.update z.2 i x)) (z.2 i) := by
    have hh := (hF z hz).1.differentiableAt (by simp)
    have hg := (hasDerivAt_const (z.2 i) z.1).prodMk (hasDerivAt_update z.2 i (z.2 i))
    exact (hh.hasFDerivAt.comp_hasDerivAt_of_eq (z.2 i) hg
      (by simp only [Function.update_eq_self,Prod.mk.eta])).differentiableAt
  refine ⟨?_,?_,?_⟩
  · apply differentiableAt_pi.mpr
    intro i
    apply differentiableAt_pi.mpr
    intro j
    exact (hb.2.2.1 (i,j) z hz).2
  · intro i
    apply differentiableAt_pi.mpr
    intro a
    apply differentiableAt_pi.mpr
    intro b
    exact hcoord (hb.2.2.1 (a,b)) i
  · intro j w
    have hh := wordCoefficient_mixed τ η p m r Ω hΩ hb j w
    exact ⟨(hh z hz).2,hcoord hh⟩

theorem regularTransportedScalar_word_expansion_of_base {N : ℕ}
    (τ : ℝ) (η p m r : ℝ → ℝ) (Ω : Set (ℂ × (Fin N → ℝ)))
    (hΩ : IsOpen Ω) (hb : MarkedBaseSmoothness τ η p m r Ω)
    (j : ℕ) (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    regularTransportedScalar τ η p m r j s θ=wordSum τ η p m r j s θ :=
  regularTransportedScalar_word_expansion τ η p m r Ω hΩ
    (wordDifferentiability_of_base τ η p m r Ω hΩ hb) j s θ hz

/-- The base hypotheses above are proved, not postulated for descendants. -/
theorem markedBaseSmoothness_of_source {N : ℕ} (τ δ : ℝ) (η p m r : ℝ → ℝ)
    (hη : ContDiff ℝ ∞ η) (hp : ContDiff ℝ ∞ p)
    (hm : ContDiff ℝ ∞ m) (hr : ContDiff ℝ ∞ r)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hR : ∀ z∈Ω, sourceCovariance z.1 (sourceCoordinate τ p m z.1 z.2)≠0) :
    MarkedBaseSmoothness τ η p m r Ω := by
  obtain ⟨hV,hD⟩ := source_generator_mixed τ δ p m hp hm Ω hΩ hpoint hR
  exact ⟨hV,hD,sourceOrdinaryKernel_mixed τ δ p m hp hm Ω hpoint,
    regularSeedCoefficient_mixed τ δ η p m r hη hp hm hr Ω hpoint⟩

/-- Actual finite transport identity under only primitive physical-domain
hypotheses. Every coefficient is computed recursively and proved smooth. -/
theorem regularTransportedScalar_word_expansion_of_source {N : ℕ}
    (τ δ : ℝ) (η p m r : ℝ → ℝ)
    (hη : ContDiff ℝ ∞ η) (hp : ContDiff ℝ ∞ p)
    (hm : ContDiff ℝ ∞ m) (hr : ContDiff ℝ ∞ r)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hR : ∀ z∈Ω, sourceCovariance z.1 (sourceCoordinate τ p m z.1 z.2)≠0)
    (j : ℕ) (t : ℂ) (θ : Fin N → ℝ) (hz : (t,θ)∈Ω) :
    regularTransportedScalar τ η p m r j t θ=wordSum τ η p m r j t θ :=
  regularTransportedScalar_word_expansion_of_base τ η p m r Ω hΩ
    (markedBaseSmoothness_of_source τ δ η p m r hη hp hm hr Ω hΩ hpoint hR) j t θ hz

end
end IsingBulk.HT22.Tail
