import IsingBulk.AnisoF002.C03.IsotropicCoareaBufferDensityFiber
import IsingBulk.AnisoF002.C03.IsotropicShellProductMeasure

/-!
# Exact fiber set measure after fixing the angular buffer
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set Metric MeasureTheory Filter

theorem exists_actual_full_density_fiber_setIntegral_buffer (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b →
      ∃ δ C W : ℝ, 0 < δ ∧ δ ≤ β ∧ 0 < C ∧ 0 < W ∧
      ∀ (N : ℕ), 0 < N → ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
      ∀ (θ : Fin N → ℝ) (i j : Fin N), i ≠ j → ∀ r γ : ℝ, 0 < r →
        (∫ t in fullExtremeFiber θ i j b β r,
          actualFullPhaseDensity (isotropicRadialParameter α ε) η τ ξ γ (constrainedAngleLine θ i j t)) ≤
        (C * N * Real.sqrt (|angularMean (fun k => θ k + b)| + r + ε) / r * (1 + |Real.log ε|)) *
          independentRemainingWeight W ε b θ i j := by
  obtain ⟨β, hβ, hβ1, hdata⟩ := exists_actual_full_density_fiber_integral_buffer α b hα hb hpoint
  refine ⟨β, hβ, hβ1, ?_⟩
  intro η hη hwidth
  obtain ⟨δ, C, W, hδ, hδβ, hC, hW, hbound⟩ := hdata η hη hwidth
  have hδ1 : δ ≤ 1 := hδβ.trans hβ1
  refine ⟨δ, C, W, hδ, hδβ, hC, hW, ?_⟩
  intro N hN ε hε hεδ τ ξ hτ hξ θ i j hij r γ hr
  by_cases hne : (fullExtremeFiber θ i j b β r).Nonempty
  · obtain ⟨A, B, hAB, he⟩ := fullExtremeFiber_eq_interval θ i j hij b β r hne
    rw [he, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hAB]
    exact hbound N hN ε hε hεδ τ ξ hτ hξ θ i j hij r γ A B hr hAB
      (by rw [he])
  · have he : fullExtremeFiber θ i j b β r = ∅ := not_nonempty_iff_eq_empty.mp hne
    rw [he, Measure.restrict_empty, integral_zero_measure]
    exact mul_nonneg (by positivity)
      (independentRemainingWeight_nonneg W ε b hW.le θ i j)

end IsingBulk.AnisoF002.Isotropic
