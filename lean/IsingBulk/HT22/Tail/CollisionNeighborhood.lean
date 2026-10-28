import IsingBulk.HT22.Tail.SourceCollision
import IsingBulk.HT22.Transport.FieldNeighborhood.PairSlopeAnalytic

namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 Geometry Filter Set
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false

theorem sourceCovariance_analyticAt {N : ℕ} (x : SourcePoint N)
    (hU : ∀ a, AnalyticAt ℂ (fun z : ℂ × ℂ => regularInverse z.1 z.2) (x.1,x.2 a)) :
    AnalyticAt ℂ (fun z : SourcePoint N => sourceCovariance z.1 z.2) x := by
  exact (Finset.univ.analyticAt_fun_sum (fun a _ =>
    Finset.univ.analyticAt_fun_sum (fun b _ =>
      ((sourceInverseCoordinate_analyticAt x a (hU a)).sub
        (sourceInverseCoordinate_analyticAt x b (hU b))).mul
      ((sourceInverseVCoordinate_analyticAt x a (hU a)).sub
        (sourceInverseVCoordinate_analyticAt x b (hU b)))))).div_const

theorem sourcePairSlope_mixed {N : ℕ}
    (τ δ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ)))
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hR : ∀ z∈Ω, sourceCovariance z.1 (sourceCoordinate τ p m z.1 z.2)≠0) :
    ∀ i j, PreferredMixedSmoothOn (fun z => sourcePairSlope τ p m z.1 z.2 i j) Ω := by
  intro i j
  apply analytic_pullback_mixed τ δ p m hp hm Ω hpoint
    (fun z => residualPairSlope z.1 z.2 i j)
  intro z hz
  exact residualPairSlope_analyticAt _ i j (framePoint_inverse_analytic (hpoint z hz)) (hR z hz)

/-- No generated descendant regularity is assumed: primitive nonzero
mixed covariance and the common actual inverse domain give the open chart. -/
theorem collision_source_neighborhood {N : ℕ}
    (τ δ c : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (s : ℂ) (θ : Fin N → ℝ) (hpoint : PreferredFramePoint τ δ p m s θ)
    (hθ : ∀ i, θ i∈Ioo (-Real.pi-δ) δ)
    (hR : sourceCovariance s (sourceCoordinate τ p m s θ)≠0)
    (hgood : ∀ i j, PreferredRightRegularPoint c s
      (preferredSourceCoordinate τ p m s θ i) (preferredSourceCoordinate τ p m s θ j)) :
    ∃ Ω : Set (ℂ × (Fin N → ℝ)), IsOpen Ω ∧ (s,θ)∈Ω ∧
      (∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2) ∧
      (∀ z∈Ω, sourceCovariance z.1 (sourceCoordinate τ p m z.1 z.2)≠0) ∧
      (∀ z∈Ω, ∀ i j, PreferredRightRegularPoint c z.1
        (preferredSourceCoordinate τ p m z.1 z.2 i) (preferredSourceCoordinate τ p m z.1 z.2 j)) := by
  have hgeom := preferredFramePoint_eventually τ δ p m hp hm s θ hpoint hθ
  have hχ := (sourceCoordinate_contDiffAt τ p m hp hm s θ hpoint.trace_im hpoint.upper).continuousAt
  have hΨ : ContinuousAt (fun z : ℂ × (Fin N → ℝ) =>
      (z.1,sourceCoordinate τ p m z.1 z.2)) (s,θ) := continuousAt_fst.prodMk hχ
  have hCov := sourceCovariance_analyticAt (s,sourceCoordinate τ p m s θ)
    (framePoint_inverse_analytic hpoint)
  have hCovC : ContinuousAt (fun z : ℂ × (Fin N → ℝ) =>
      sourceCovariance z.1 (sourceCoordinate τ p m z.1 z.2)) (s,θ) :=
    ContinuousAt.comp (f := fun z : ℂ × (Fin N → ℝ) => (z.1,sourceCoordinate τ p m z.1 z.2))
      (g := fun z : SourcePoint N => sourceCovariance z.1 z.2) hCov.continuousAt hΨ
  have hRa := hCovC.eventually_ne hR
  have hq := (preferredSourceCoordinate_contDiffAt τ p m hp hm s θ hpoint.trace_im hpoint.upper).continuousAt
  have hGa : ∀ᶠ z : ℂ × (Fin N → ℝ) in 𝓝 (s,θ), ∀ i j,
      PreferredRightRegularPoint c z.1 (preferredSourceCoordinate τ p m z.1 z.2 i)
        (preferredSourceCoordinate τ p m z.1 z.2 j) := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    have hmap : ContinuousAt (fun z : ℂ × (Fin N → ℝ) =>
        (z.1,preferredSourceCoordinate τ p m z.1 z.2 i,
          preferredSourceCoordinate τ p m z.1 z.2 j)) (s,θ) :=
      continuousAt_fst.prodMk (((continuous_apply i).continuousAt.comp hq).prodMk
        ((continuous_apply j).continuousAt.comp hq))
    exact hmap.tendsto.eventually ((preferredRightRegularPoint_isOpen c).mem_nhds (hgood i j))
  obtain ⟨Ω,hΩsub,hΩ,hz⟩ := mem_nhds_iff.mp (hgeom.and (hRa.and hGa))
  exact ⟨Ω,hΩ,hz,fun z hz => (hΩsub hz).1,fun z hz => (hΩsub hz).2.1,
    fun z hz => (hΩsub hz).2.2⟩

end
end IsingBulk.HT22.Tail
