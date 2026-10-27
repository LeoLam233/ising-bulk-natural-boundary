import IsingBulk.Preferred22.SourceMixedFactors
import IsingBulk.Preferred22.SourceFrameGeometry
import IsingBulk.Preferred22.CollectiveAnalyticSource

/-! Exact all-order signed-minor expansion at the actual positive-epsilon
balanced source. No descendant differentiability or base regularity is
assumed at the endpoint. Bounds for the generated scalar coefficients are
a further quantitative obligation. -/
namespace IsingBulk.Preferred22
noncomputable section
open Filter Set Metric
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

theorem preferred_source_marked_word_expansion {N : ℕ}
    (τ δ : ℝ) (η p m r : ℝ → ℝ)
    (hη : ContDiff ℝ ∞ η) (hp : ContDiff ℝ ∞ p)
    (hm : ContDiff ℝ ∞ m) (hr : ContDiff ℝ ∞ r)
    (s : ℂ) (θ : Fin N → ℝ) (hpoint : PreferredFramePoint τ δ p m s θ)
    (hθ : ∀ i, θ i∈Ioo (-Real.pi-δ) δ)
    (hB : AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) => preferredResidualCollective x.1 x.2)
      (s,preferredSourceCoordinate τ p m s θ)) (j : ℕ) :
    preferredRegularTransportedScalar τ η p m r j s θ=preferredWordSum τ η p m r j s θ := by
  have hgeom := preferredFramePoint_eventually τ δ p m hp hm s θ hpoint hθ
  have hχ := (preferredSourceCoordinate_contDiffAt τ p m hp hm s θ hpoint.trace_im hpoint.upper).continuousAt
  have hΨ : ContinuousAt (fun z : ℂ × (Fin N → ℝ) =>
      (z.1,preferredSourceCoordinate τ p m z.1 z.2)) (s,θ) := continuousAt_fst.prodMk hχ
  have ha := hΨ.tendsto.eventually hB.eventually_analyticAt
  obtain ⟨Ω,hΩsub,hΩ,hz⟩ := _root_.mem_nhds_iff.mp (hgeom.and ha)
  exact preferredRegularTransportedScalar_word_expansion_of_base τ η p m r Ω hΩ
    (preferredMarkedBaseSmoothness_of_geometry τ δ η p m r hη hp hm hr Ω hΩ
      (fun z hz => (hΩsub hz).1) (fun z hz => (hΩsub hz).2)) j s θ hz

/-- The finite signed-word formula holds for the literal source scalar at
every order, with one physical source regime chosen before the order and N.
All occupancies and all original smooth real cutoff derivatives remain. -/
theorem preferred_actual_marked_word_expansion (d : PreferredBranchData) :
    ∃ cap : ℝ, 0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d, B.delta<cap →
      ∃ ε₀ τ₀ δB : ℝ, 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
        ∀ N : ℕ, 0<N → ∀ ε τ : ℝ, 0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
        ∀ θ : Fin N → ℝ,
        (∀ i, -δB≤θ i+d.b ∧ θ i+d.b≤d.b+B.delta) →
        0<preferredAngularDiameter θ →
        ∀ η r : ℝ → ℝ, ContDiff ℝ ∞ η → ContDiff ℝ ∞ r → ∀ j : ℕ,
        preferredRegularTransportedScalar τ η B.p B.m r j
            (IsingBulk.Branch.radialParameter d.alpha ε) θ=
          preferredWordSum τ η B.p B.m r j (IsingBulk.Branch.radialParameter d.alpha ε) θ := by
  obtain ⟨cap,hcap,hcapa,hlocal⟩ := preferred_actual_collective_neighborhood d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hBcap
  obtain ⟨η₀,M,ε₁,τ₁,δB,hη₀,hM,hε₁,hτ₁,hδB,hδBB,hneigh⟩ := hlocal B hBcap
  obtain ⟨δ,ε₂,τ₂,hδ,hδa,hε₂,hτ₂,hframe⟩ := preferred_actual_frame_points d B
  refine ⟨min ε₁ ε₂,min τ₁ τ₂,δB,lt_min hε₁ hε₂,lt_min hτ₁ hτ₂,hδB,hδBB,?_⟩
  intro N hN ε τ hε hεr hτ hτr θ hθ hdiam η r hη hr j
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  let q := preferredSourceCoordinate τ B.p B.m s θ
  have hB : AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => preferredResidualCollective z.1 z.2) (s,q) :=
    preferredResidualCollective_analyticAt_of_rescaled hN s q η₀ (preferredAngularDiameter θ) hη₀ hdiam
      ((hneigh N hN ε τ hε (hεr.trans_le (min_le_left _ _)) hτ
        (hτr.trans_le (min_le_left _ _)) θ hθ hdiam).1 0 (by simp))
  obtain ⟨hpoint,hθstrict⟩ := hframe δB hδB hδBB N hN ε τ hε
    (hεr.trans_le (min_le_right _ _)) hτ (hτr.trans_le (min_le_right _ _)) θ hθ
  exact preferred_source_marked_word_expansion τ δ η B.p B.m r hη B.smooth B.m_smooth hr
    s θ hpoint hθstrict hB j

end
end IsingBulk.Preferred22
