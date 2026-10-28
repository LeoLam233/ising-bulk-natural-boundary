import IsingBulk.Preferred22.ZerothSourceBound
import IsingBulk.HT22.Tail.ActualRightChart
import IsingBulk.HT22.Tail.PunctureFlux

namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 Geometry Set
open scoped ContDiff Topology BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- Primitive physical source neighborhood, excluding only full covariance. -/
def RegularPoint {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ) (s : ℂ) (θ : Fin N → ℝ) : Prop :=
  ∃ δ : ℝ, ∃ Ω : Set (ℂ × (Fin N → ℝ)), IsOpen Ω ∧ (s,θ)∈Ω ∧
    (∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2) ∧
    (∀ z∈Ω, sourceCovariance z.1 (sourceCoordinate τ p m z.1 z.2)≠0)

theorem transportedDensity_regularPoint {N : ℕ} (hN : 0<N) (σ : ℂ) (hσ : ‖σ‖≤1)
    (τ : ℝ) (η p m r : ℝ → ℝ)
    (hη : ContDiff ℝ ∞ η) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) (hr : ContDiff ℝ ∞ r)
    (j : ℕ) (s : ℂ) (θ : Fin N → ℝ) (hreg : RegularPoint τ p m s θ) :
    ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) => transportedDensity σ τ η p m r j z.1 z.2) (s,θ) ∧
    DifferentiableAt ℂ (fun t => transportedDensity σ τ η p m r j t θ) s := by
  obtain ⟨δ,Ω,hΩ,hz,hpoint,hR⟩ := hreg
  exact transportedDensity_mixed hN σ hσ τ δ η p m r hη hp hm hr Ω hΩ hpoint hR j _ hz

theorem angularField_regularPoint {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (s : ℂ) (θ : Fin N → ℝ) (hreg : RegularPoint τ p m s θ) (i : Fin N) :
    ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) => angularField τ p m z.1 z.2 i) (s,θ) := by
  obtain ⟨δ,Ω,hΩ,hz,hpoint,hR⟩ := hreg
  exact ((source_generator_mixed τ δ p m hp hm Ω hΩ hpoint hR).1 i _ hz).1

theorem angularField_regularPoint_tangent {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (s : ℂ) (θ : Fin N → ℝ) (hreg : RegularPoint τ p m s θ) :
    (∑ i,angularField τ p m s θ i)=0 := by
  obtain ⟨δ,Ω,hΩ,hz,hpoint,hR⟩ := hreg
  apply preferredAngularRepresentative_tangent (preferredContourMatrix τ p m θ)
    (fun a => inverseT s (sourceCoordinate τ p m s θ a))
    (fun a => inverseV s (sourceCoordinate τ p m s θ a))
    (residualField s (sourceCoordinate τ p m s θ))
  · intro j
    rw [preferredContourMatrix_eq_full]
    exact fullAngularJacobian_column_sum 1 τ p m θ j
  · exact (hpoint (s,θ) hz).matrix
  · exact sourceResidual_constraint s (sourceCoordinate τ p m s θ) (hR (s,θ) hz)

/-- Every actual right-support nonequality point satisfies the primitive
regularity interface, with thresholds chosen before particle and jet order. -/
theorem actual_regularPoint (d : PreferredBranchData) :
    ∃ cap : ℝ, 0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d, B.delta<cap →
      ∃ ε₀ τ₀ δB : ℝ, 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
        ∀ N : ℕ, 0<N → ∀ ε τ : ℝ, 0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
        ∀ θ∈preferredRightAngularBox d B.delta δB N, 0<preferredAngularDiameter θ →
          RegularPoint τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ := by
  obtain ⟨cap,hcap,hcapa,hbound⟩ := actual_right_source_chart d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hB
  obtain ⟨c,δ,e,t,b,hc,he,ht,hb,hbB,hchart⟩ := hbound B hB
  refine ⟨e,t,b,he,ht,hb,hbB,?_⟩
  intro N hN ε τ hε hεr hτ hτr θ hθ hdiam
  obtain ⟨Ω,hΩ,hz,hpoint,hR,_⟩ := hchart N hN ε τ hε hεr hτ hτr θ
    (fun i => ⟨by linarith [(hθ i).1],by linarith [(hθ i).2]⟩) hdiam
  exact ⟨δ,Ω,hΩ,hz,hpoint,hR⟩

end
end IsingBulk.HT22.Tail
