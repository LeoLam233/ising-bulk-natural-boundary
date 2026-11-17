import IsingBulk.AnisoF002.C03.IsotropicTransportDensity
import IsingBulk.AnisoF002.C03.IsotropicCoareaBuffers
import IsingBulk.AnisoF002.C03.IsotropicActualDeterminantBound

/-!
# The literal complete current multiplier in the proved coarea density

The actual coordinate determinant factors through the full balanced
Jacobian. The complete signed kernel has numerator at most two on the
physical sheet. Thus the earlier coarea integral controls the genuine
transported physical density, including the entire determinant.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Metric
open scoped Topology BigOperators

theorem actualCoordinateMultiplier_eq_phaseSlope {N : ℕ} (s : ℂ) (η τ ξ : ℝ)
    (θ : Fin N → ℝ) (i : Fin N) :
    actualCoordinateMultiplier η τ ξ (s, θ) i = 1 + actualPhaseSlope s η τ ξ θ i := by
  unfold actualCoordinateMultiplier actualPhaseSlope physicalPhaseAngleSlope actualPhysicalPhase
  ring

theorem actualTransportDensityMultiplier_coarea_bound {N : ℕ} (s σ : ℂ)
    (hs : 0 < s.im) (hσ : ‖σ‖ ≤ 1) (η τ ξ : ℝ)
    (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ) (θ : Fin N → ℝ) :
    ‖actualTransportDensityMultiplier σ η τ ξ (s, θ)‖ ≤
      2 * ‖(actualBalancedJacobian η τ ξ θ).det‖ * actualSignedFullDensity s σ η τ ξ θ := by
  have hsheet (i : Fin N) := actual_balanced_homotopy_sheet s hs η τ ξ hη hτ hξ θ i
  have hprod : ‖∏ i, isotropicInteriorRoot (s, actualHomotopyAngle η τ ξ θ i)‖ ≤ 1 := by
    rw [norm_prod]
    have hh := Finset.prod_le_prod₀ (s := (Finset.univ : Finset (Fin N)))
      (f := fun i => ‖isotropicInteriorRoot (s, actualHomotopyAngle η τ ξ θ i)‖)
      (g := fun _ => (1 : ℝ)) (fun _ _ => norm_nonneg _)
      (fun i _ => (RegularTail.upperEdgeRoot_norm_lt_one (hsheet i)).le)
    simpa only [Finset.prod_const_one] using hh
  have hnum : ‖1 + σ * ∏ i, isotropicInteriorRoot (s, actualHomotopyAngle η τ ξ θ i)‖ ≤ 2 := by
    apply (norm_add_le _ _).trans
    rw [norm_one, norm_mul]
    have hh := mul_le_mul hσ hprod (norm_nonneg _) zero_le_one
    linarith
  rw [actualTransportDensityMultiplier, norm_mul,
    actualCoordinateDeterminant_factorization η τ ξ (s, θ) hsheet,
    norm_mul, norm_prod, actualSignedProductKernel_eq_physical, norm_div]
  simp_rw [actualCoordinateMultiplier_eq_phaseSlope]
  calc
    _ ≤ ‖(actualBalancedJacobian η τ ξ θ).det‖ * (∏ i, ‖1 + actualPhaseSlope s η τ ξ θ i‖) *
      (2 / ‖1 - σ * ∏ i, isotropicInteriorRoot (s, actualHomotopyAngle η τ ξ θ i)‖) := by gcongr
    _ = _ := by unfold actualSignedFullDensity; ring

theorem exists_actual_current_multiplier_coarea_bound (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ (N : ℕ), 0 < N →
      ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
      ∀ s σ : ℂ, 0 < s.im → ‖σ‖ ≤ 1 → ∀ θ : Fin N → ℝ,
        ‖actualTransportDensityMultiplier σ η τ ξ (s, θ)‖ ≤
          (2 : ℝ) ^ (N + 1) * actualSignedFullDensity s σ η τ ξ θ := by
  obtain ⟨δ, hδ, hδ1, hdet⟩ := exists_actual_balanced_determinant_bound η
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro N hN τ ξ hτ hξ s σ hs hσ θ
  apply (actualTransportDensityMultiplier_coarea_bound s σ hs hσ η τ ξ hη hτ.1 hξ.1 θ).trans
  calc
    _ ≤ 2 * (2 : ℝ) ^ N * actualSignedFullDensity s σ η τ ξ θ := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hdet N hN τ ξ hτ hξ θ) (by norm_num))
        (actualSignedFullDensity_nonneg _ _ _ _ _ _)
    _ = _ := by rw [pow_succ]; ring

end
end IsingBulk.AnisoF002.Isotropic
