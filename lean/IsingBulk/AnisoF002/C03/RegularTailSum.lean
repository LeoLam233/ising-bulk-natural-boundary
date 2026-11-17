import IsingBulk.AnisoF002.C03.RegularCoefficientNormal
import IsingBulk.AnisoF002.RegularTail.CollisionBudget

/-!
# Actual infinite-tail derivatives on the regular inward path

The infinite tail is the sum of every larger same-parity complete
coefficient.  Its analyticity and derivative identities follow on the
common complex disks.  The fixed-block estimate then bounds derivatives
of this actual sum uniformly up to the singular boundary.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open scoped Topology

/-- The first coefficient has m+1 particles; all later counts increase
by two.  For first resonant n, taking m=n+1 includes precisely n+2+2r. -/
def edgeParticleTail (c a : ℂ → ℂ) (m : ℕ) (t : ℂ) : ℂ :=
  ∑' n : ℕ, edgeParticleCoefficient c a (m + 2 * n) t

namespace RegularEdgeCompleteControl
variable {b : ℝ} {a : ℂ → ℂ} (d : RegularEdgeCompleteControl b a)

theorem particleTail_analytic_inward (m : ℕ) {eps : ℝ}
    (he : 0 < eps) (he0 : eps ≤ d.eps0) :
    AnalyticAt ℂ (edgeParticleTail (affineEdgeCenter b) a m) ((eps : ℂ) * Complex.I) := by
  obtain ⟨r, hr, M, hM, hf, hb⟩ := d.exists_particle_subseries_common_disk m he he0
  exact analyticAt_tsum_of_common_disk hr hM hf hb

theorem particleTail_iteratedDeriv_inward (m j : ℕ) {eps : ℝ}
    (he : 0 < eps) (he0 : eps ≤ d.eps0) :
    iteratedDeriv j (edgeParticleTail (affineEdgeCenter b) a m) ((eps : ℂ) * Complex.I) =
      ∑' n : ℕ, iteratedDeriv j (edgeParticleCoefficient (affineEdgeCenter b) a (m + 2 * n))
        ((eps : ℂ) * Complex.I) := by
  obtain ⟨r, hr, M, hM, hf, hb⟩ := d.exists_particle_subseries_common_disk m he he0
  exact iteratedDeriv_tsum_of_common_disk hr hM hf hb (Metric.mem_ball_self (half_pos hr)) j

/-- The complete differentiated tail, including every intermediate and
large index, is uniformly bounded under the exact m-dimensional budget. -/
theorem particleTail_derivative_uniform {m j : ℕ}
    (hm : 0 < m) (hbudget : 2 * (j + 1) < m ^ 2) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ eps : ℝ, 0 < eps → eps ≤ d.eps0 →
      ‖iteratedDeriv j (edgeParticleTail (affineEdgeCenter b) a m)
        ((eps : ℂ) * Complex.I)‖ ≤ M := by
  obtain ⟨M, hM, hb⟩ := d.complete_differentiated_tail_uniform hm hbudget
  refine ⟨M, hM, ?_⟩
  intro eps he he0
  obtain ⟨hs, _, hsum⟩ := hb eps he he0
  simp_rw [edgeConstrainedCoefficient_eq_particle] at hs hsum
  rw [d.particleTail_iteratedDeriv_inward m j he he0]
  apply (norm_tsum_le_tsum_norm hs).trans
  have hn : 0 ≤ ∑' n : ℕ,
      ‖iteratedDeriv j (edgeParticleCoefficient (affineEdgeCenter b) a (m + (2 * n + 1)))
        ((eps : ℂ) * Complex.I)‖ := tsum_nonneg fun _ => norm_nonneg _
  linarith

/-- The exact derivative budget for every order demanded by either
printed parity-specific first-singularity formula. -/
theorem selected_tail_derivative_uniform {n j : ℕ}
    (hn : 1 ≤ n) (hj : 2 * j ≤ n ^ 2) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ eps : ℝ, 0 < eps → eps ≤ d.eps0 →
      ‖iteratedDeriv j (edgeParticleTail (affineEdgeCenter b) a (n + 1))
        ((eps : ℂ) * Complex.I)‖ ≤ M :=
  d.particleTail_derivative_uniform (by omega) (by nlinarith)

theorem odd_selected_tail_all_orders {n j : ℕ}
    (hn : 1 ≤ n) (hj : j ≤ oddTopOrder n) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ eps : ℝ, 0 < eps → eps ≤ d.eps0 →
      ‖iteratedDeriv j (edgeParticleTail (affineEdgeCenter b) a (n + 1))
        ((eps : ℂ) * Complex.I)‖ ≤ M :=
  d.selected_tail_derivative_uniform hn (odd_derivative_budget hj)

theorem even_selected_tail_all_orders {n j : ℕ}
    (hn : 1 ≤ n) (hj : j ≤ evenTopOrder n) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ eps : ℝ, 0 < eps → eps ≤ d.eps0 →
      ‖iteratedDeriv j (edgeParticleTail (affineEdgeCenter b) a (n + 1))
        ((eps : ℂ) * Complex.I)‖ ≤ M :=
  d.selected_tail_derivative_uniform hn (even_derivative_budget hj)

end RegularEdgeCompleteControl
end
end IsingBulk.AnisoF002.RegularTail.C03
