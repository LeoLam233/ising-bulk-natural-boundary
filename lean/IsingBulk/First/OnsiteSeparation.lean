import IsingBulk.First.OnsiteFactorization

/-! The onsite source has a uniform local separating direction at every unit
configuration on a positive trace level below two. -/
namespace IsingBulk.First
noncomputable section
open Filter Set
open scoped Topology

theorem onsite_active_uniform_separator {N : ℕ} {x y : Fin N → ℂ} {S : ℝ}
    (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1) (hS : 0 < S ∧ S < 2) :
    ∃ (e : DoubleAngularVector N) (δ : ℝ), 0 < δ ∧
      ∀ᶠ q : ℝ × (Fin N → ℂ) × (Fin N → ℂ) in 𝓝 (1, x, y),
        ∀ i : OnsiteFactorIndex N, singularFactorActive x y S (.inr i) →
          δ < angularDot e (dampedSingularVector q.1 q.2.1 q.2.2 (.inr i)) := by
  obtain ⟨f, δ, hδ, hf⟩ := onsite_separating_functional hx hy hS
  refine ⟨separatingDirection f, δ / 2, by linarith, ?_⟩
  rw [Filter.eventually_all]
  intro i
  by_cases hi : singularFactorActive x y S (.inr i)
  · have hc := f.continuous.continuousAt.comp (dampedSingularVector_continuousAt x y (.inr i))
    have hbase : δ / 2 < f (dampedSingularVector 1 x y (.inr i)) := by
      rw [dampedSingularVector_one hi]
      linarith [hf i hi]
    have he := hc.preimage_mem_nhds (Ioi_mem_nhds hbase)
    filter_upwards [he] with q hq
    intro _
    rw [angularDot_separatingDirection]
    exact hq
  · exact Filter.Eventually.of_forall (fun _ hi' => False.elim (hi hi'))


end
end IsingBulk.First
