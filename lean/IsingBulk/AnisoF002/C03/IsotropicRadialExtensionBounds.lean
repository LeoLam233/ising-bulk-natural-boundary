import IsingBulk.AnisoF002.C03.IsotropicNonresonantCoincidence
import IsingBulk.AnisoF002.C03.IsotropicCollisionFiniteComplement

/-!
# Actual parameter-jet bounds from a genuine upper-side continuation

Ordinary derivatives agree on the actual upper neighborhoods by germ
equality. The analytic extension controls those jets uniformly on a
smaller disk, then the exact original radial path enters that disk.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter Metric
open scoped Topology

theorem analytic_upper_extension_jet_bound {f G : ℂ → ℂ} {S₀ : ℂ} {d : ℝ}
    (hd : 0 < d) (hG : AnalyticAt ℂ G S₀)
    (he : ∀ S : ℂ, dist S S₀ ≤ d → 0 < S.im → G S = f S) (j : ℕ) :
    ∃ e A : ℝ, 0 < e ∧ 0 < A ∧ ∀ S : ℂ, dist S S₀ < e → 0 < S.im →
      ‖iteratedDeriv j f S‖ ≤ A := by
  have hGj : ContinuousAt (iteratedDeriv j G) S₀ := by
    simpa only [iteratedDeriv_eq_iterate] using (hG.iterated_deriv j).continuousAt
  have hbound : ∀ᶠ S in 𝓝 S₀, ‖iteratedDeriv j G S‖ < ‖iteratedDeriv j G S₀‖ + 1 :=
    hGj.norm.eventually (Iio_mem_nhds (by linarith))
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff.mp hbound
  refine ⟨min r d, ‖iteratedDeriv j G S₀‖ + 1, lt_min hr hd, by positivity, ?_⟩
  intro S hS him
  have hSd : S ∈ ball S₀ d := hS.trans_le (min_le_right _ _)
  have hfg : f =ᶠ[𝓝 S] G := by
    filter_upwards [isOpen_ball.mem_nhds hSd,
      (isOpen_lt continuous_const Complex.continuous_im).mem_nhds him] with T hT hTi
    exact (he T (Metric.mem_ball.mp hT).le hTi).symm
  rw [(hfg.iteratedDeriv j).eq_of_nhds]
  exact (hb (hS.trans_le (min_le_left _ _))).le

theorem analytic_upper_extension_radial_jet_bound {f G : ℂ → ℂ} {α d : ℝ}
    (hα : 0 < α ∧ α < Real.pi) (hd : 0 < d)
    (hG : AnalyticAt ℂ G ((2 * Real.cos α : ℝ) : ℂ))
    (he : ∀ S : ℂ, dist S ((2 * Real.cos α : ℝ) : ℂ) ≤ d → 0 < S.im → G S = f S)
    (j : ℕ) : ∃ ε₀ A : ℝ, 0 < ε₀ ∧ 0 < A ∧ ∀ ε ∈ Ioo 0 ε₀,
      ‖iteratedDeriv j f (isotropicRadialParameter α ε)‖ ≤ A := by
  obtain ⟨e, A, he0, hA, hb⟩ := analytic_upper_extension_jet_bound hd hG he j
  refine ⟨min 1 (e / 4), A, lt_min zero_lt_one (by positivity), hA, ?_⟩
  intro ε hε
  have hε1 : ε ≤ 1 := hε.2.le.trans (min_le_left _ _)
  have hh := isotropicRadialParameter_estimates α ε hα hε.1 hε1
  exact hb _ (hh.2.2.2.2.trans_lt (by have := hε.2.trans_le (min_le_right _ _); linarith))
    hh.2.2.2.1

theorem exists_actual_nonresonant_near_jet_bound (n : ℕ) (α μ η τ ξ : ℝ) (σ : ℂ)
    (hα : 0 < α ∧ α < Real.pi) (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ)
    (hx : -1 < 2 * Real.cos α - Real.cos μ) (hx1 : 2 * Real.cos α - Real.cos μ ≠ 1)
    (hden : 1 - σ * upperBoundaryRoot (2 * Real.cos α - Real.cos μ) ^ (n + 1) ≠ 0) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∀ g : (Fin (n + 1) → ℝ) → ℂ, Continuous g → ∀ j : ℕ,
      ∃ ε₀ A : ℝ, 0 < ε₀ ∧ 0 < A ∧ ∀ ε ∈ Ioo 0 ε₀,
        ‖iteratedDeriv j (centeredWeightedPhysicalCoefficient η τ ξ μ σ (weightedCollisionNear r g))
          (isotropicRadialParameter α ε)‖ ≤ A := by
  obtain ⟨d, hd, hext⟩ := exists_actual_nonresonant_coincidence_extension
    n (2 * Real.cos α) μ η τ ξ σ hη hτ hξ hx hx1 hden
  refine ⟨d ^ 2 / 4, by positivity, ?_⟩
  intro r hr hrd g hg j
  obtain ⟨G, hG, heq⟩ := hext (2 * r) (by positivity) (by linarith) (weightedCollisionNear r g)
    (hg.mul (Complex.continuous_ofReal.comp (collisionNearCutoff_contDiff (n + 1) r).continuous))
    (fun q hq => by
      have hh := (weightedCollisionNear_tsupport hr g (subset_closure hq)).2
      simpa only [angularCenteredQuadratic_centered] using hh)
  exact analytic_upper_extension_radial_jet_bound hα hd hG heq j

end
end IsingBulk.AnisoF002.Isotropic
