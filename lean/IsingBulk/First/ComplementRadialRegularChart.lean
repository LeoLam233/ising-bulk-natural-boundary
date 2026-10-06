import IsingBulk.First.ComplementRadialCompact

/-! Uniform regularity of the original inactive factors on a fixed chart and
closed source radial interval. This does not require nonstationarity. -/
namespace IsingBulk.First
noncomputable section
open Set Filter
open scoped Topology

theorem source_radial_regular_chart {N : ℕ} (θ S : ℝ) (hθ : 0 < Real.sin θ)
    (hS : sourceS (Complex.exp ((θ : ℂ)*Complex.I)) = (S : ℂ))
    (u₀ : DoubleAngularVector N) (J : Finset (SingularFactorIndex N))
    (hJ : ∀ f, f ∈ J ↔ singularFactorActive (angleTuple 1 u₀.1) (angleTuple 1 u₀.2) S f) :
    ∃ γ ε₀ : ℝ, 0 < γ ∧ 0 < ε₀ ∧
      (∀ ε ∈ Icc 0 ε₀, 0 < (sourceRadialPair θ ε).1 ∧ (sourceRadialPair θ ε).1 ≤ 1 ∧
        (sourceRadialPair θ ε).2 ≠ 0 ∧ (sourceRadialPair θ ε).1⁻¹-(sourceRadialPair θ ε).1 ≤
          (sourceS (sourceRadialPair θ ε).2).im) ∧
      ∀ ε ∈ Icc 0 ε₀, ∀ u ∈ Metric.closedBall u₀ γ,
        (sourceRadialPair θ ε,u) ∈ sourceInactiveDomain J := by
  have hdom := selected_source_mem_inactiveDomain (Complex.exp ((θ : ℂ)*Complex.I)) S
    (Complex.exp_ne_zero _) hS u₀ J hJ
  have hn := (sourceInactiveDomain_isOpen J).mem_nhds hdom
  obtain ⟨ρ,hρ,hball⟩ := Metric.eventually_nhds_iff.mp hn
  obtain ⟨d₀,hd₀,hdamp⟩ := sourceRadialPair_closed_damping hθ
  have he : ∀ᶠ ε : ℝ in 𝓝 0,
      dist (sourceRadialPair θ ε) (sourceRadialPair θ 0) < ρ/2 :=
    (sourceRadialPair_continuous θ).continuousAt.preimage_mem_nhds
      (Metric.ball_mem_nhds _ (by positivity))
  obtain ⟨d,hd,hclose⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨ρ/2,min d₀ (d/2),by positivity,lt_min hd₀ (by positivity),?_,?_⟩
  · intro ε hε
    exact hdamp ε ⟨hε.1,hε.2.trans (min_le_left _ _)⟩
  · intro ε hε u hu
    apply hball
    rw [Prod.dist_eq, max_lt_iff]
    have hp : dist (sourceRadialPair θ ε) (1,Complex.exp ((θ : ℂ)*Complex.I)) < ρ/2 := by
      rw [← sourceRadialPair_zero]
      apply hclose
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hε.1]
      exact hε.2.trans_lt ((min_le_right _ _).trans_lt (by linarith))
    exact ⟨hp.trans (by linarith), (Metric.mem_closedBall.mp hu).trans_lt (by linarith)⟩

end
end IsingBulk.First
