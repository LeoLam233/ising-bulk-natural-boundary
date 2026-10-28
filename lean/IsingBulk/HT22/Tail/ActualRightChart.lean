import IsingBulk.HT22.Tail.ActualCollisionChart

namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 Geometry Set
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

/-- The regular open chart exists at every nonequality point of the whole
actual right support, not merely at a preselected dyadic shell. -/
theorem actual_right_source_chart (d : PreferredBranchData) :
    ∃ cap : ℝ, 0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d, B.delta<cap →
      ∃ c δ ε₀ τ₀ δB : ℝ, 0<c ∧ 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
        ∀ N : ℕ, 0<N → ∀ ε τ : ℝ, 0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
        ∀ θ : Fin N → ℝ,
        (∀ i, -δB≤θ i+d.b ∧ θ i+d.b≤d.b+B.delta) →
        0<preferredAngularDiameter θ →
        ∃ Ω : Set (ℂ × (Fin N → ℝ)), IsOpen Ω ∧
          (IsingBulk.Branch.radialParameter d.alpha ε,θ)∈Ω ∧
          (∀ z∈Ω, PreferredFramePoint τ δ B.p B.m z.1 z.2) ∧
          (∀ z∈Ω, sourceCovariance z.1 (sourceCoordinate τ B.p B.m z.1 z.2)≠0) ∧
          (∀ z∈Ω, ∀ a b, PreferredRightRegularPoint c z.1
            (preferredSourceCoordinate τ B.p B.m z.1 z.2 a)
            (preferredSourceCoordinate τ B.p B.m z.1 z.2 b)) := by
  obtain ⟨cap,hcap,hcapa,hbound⟩ := actual_collision_source_chart d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hB
  obtain ⟨c,δ,e,t,b,hc,he,ht,hb,hbB,hchart⟩ := hbound B hB
  refine ⟨c,δ,e,t,b,hc,he,ht,hb,hbB,?_⟩
  intro N hN ε τ hε hεr hτ hτr θ hθ hdiam
  have hnon : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0,hN⟩,Finset.mem_univ _⟩
  obtain ⟨i,_,hmin⟩ := Finset.exists_min_image Finset.univ θ hnon
  obtain ⟨a,_,hmax⟩ := Finset.exists_max_image Finset.univ θ hnon
  have hext (v : Fin N) : θ i≤θ v ∧ θ v≤θ a :=
    ⟨hmin v (Finset.mem_univ _),hmax v (Finset.mem_univ _)⟩
  have hgap : 0<θ a-θ i := by
    by_contra hn
    have he : θ a=θ i := by linarith [(hext a).1]
    have hz : preferredAngularDiameter θ≤0 := by
      apply Metric.diam_le_of_forall_dist_le le_rfl
      rintro _ ⟨v,rfl⟩ _ ⟨w,rfl⟩
      have hv : θ v=θ i := by linarith [(hext v).1,(hext v).2]
      have hw : θ w=θ i := by linarith [(hext w).1,(hext w).2]
      simp only [hv,hw,dist_self,le_refl]
    linarith
  apply hchart N hN ε τ (θ i+d.b) (θ a-θ i) hε hεr hτ hτr hgap θ hθ _ i a hext le_rfl
  intro v
  constructor <;> linarith [(hext v).1,(hext v).2]

end
end IsingBulk.HT22.Tail
