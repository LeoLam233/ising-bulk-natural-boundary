import IsingBulk.AnisoF002.C03.IsotropicActualRealJetBuffer

/-!
# Smooth geometric multipliers at every interior physical parameter

The full coordinate determinant and complete signed product kernel are
smooth at total coincidences as well. Only the transported covariance
amplitude needs the subsequent removable-value argument.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set
open scoped Topology BigOperators ContDiff

variable {N : ℕ}

theorem actual_regular_map_interior_smooth (η τ ξ : ℝ)
    (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ)
    (q : ℂ × (Fin N → ℝ)) (hq : 0 < q.1.im) :
    ContDiffAt ℝ ∞ (regularJointMap (actualPhysicalCoordinate η τ ξ)) q := by
  exact contDiffAt_fst.prodMk (contDiffAt_pi.mpr (fun i =>
    actualPhysicalCoordinate_contDiffAt η τ ξ i q ⊤
      (actual_balanced_homotopy_sheet q.1 hq η τ ξ hη hτ hξ q.2 i)))

theorem actualCoordinateDeterminant_interior_smooth (η τ ξ : ℝ)
    (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ)
    (q : ℂ × (Fin N → ℝ)) (hq : 0 < q.1.im) :
    ContDiffAt ℝ ∞ (actualCoordinateDeterminant η τ ξ) q := by
  apply scalarMatrixDet_contDiffAt _ q
  exact scalarCoordinateMatrix_contDiffAt (actualPhysicalCoordinate η τ ξ) actualAngularDirection q
    (fun i => actualPhysicalCoordinate_contDiffAt η τ ξ i q ⊤
      (actual_balanced_homotopy_sheet q.1 hq η τ ξ hη hτ hξ q.2 i))

theorem actualTotalPhase_interior_smooth (η τ ξ : ℝ)
    (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ)
    (q : ℂ × (Fin N → ℝ)) (hq : 0 < q.1.im) :
    ContDiffAt ℝ ∞ (actualTotalPhase η τ ξ) q := by
  rw [funext (actualTotalPhase_eq_coordinates η τ ξ)]
  apply (ContDiffAt.sum (fun i _ => actualPhysicalCoordinate_contDiffAt η τ ξ i q ⊤
    (actual_balanced_homotopy_sheet q.1 hq η τ ξ hη hτ hξ q.2 i))).sub
  rw [← funext realAngularSumLinear_apply]
  exact (realAngularSumLinear (ι := Fin N)).contDiff.contDiffAt

theorem actualSignedProductKernel_interior_smooth (hN : 0 < N) (σ : ℂ) (hσ : ‖σ‖ ≤ 1)
    (η τ ξ : ℝ) (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ)
    (q : ℂ × (Fin N → ℝ)) (hq : 0 < q.1.im) :
    ContDiffAt ℝ ∞ (actualSignedProductKernel σ η τ ξ) q := by
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hd := actualSignedProductKernel_denominator σ hσ η τ ξ hη hτ hξ q hq
  exact (physicalPhaseKernel_analyticAt σ (actualTotalPhase η τ ξ q) hd).restrictScalars.contDiffAt.comp q
    (actualTotalPhase_interior_smooth η τ ξ hη hτ hξ q hq)

def actualTransportDensityMultiplier (σ : ℂ) (η τ ξ : ℝ) (q : ℂ × (Fin N → ℝ)) : ℂ :=
  actualCoordinateDeterminant η τ ξ q * actualSignedProductKernel σ η τ ξ q

theorem actualTransportDensityMultiplier_interior_smooth (hN : 0 < N) (σ : ℂ) (hσ : ‖σ‖ ≤ 1)
    (η τ ξ : ℝ) (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ)
    (q : ℂ × (Fin N → ℝ)) (hq : 0 < q.1.im) :
    ContDiffAt ℝ ∞ (actualTransportDensityMultiplier σ η τ ξ) q :=
  (actualCoordinateDeterminant_interior_smooth η τ ξ hη hτ hξ q hq).mul
    (actualSignedProductKernel_interior_smooth hN σ hσ η τ ξ hη hτ hξ q hq)

theorem compact_interior_multiplier_first_jets (hN : 0 < N) (σ : ℂ) (hσ : ‖σ‖ ≤ 1)
    (η τ ξ : ℝ) (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ)
    (K : Set (ℂ × (Fin N → ℝ))) (hK : IsCompact K) (hupper : ∀ q ∈ K, 0 < q.1.im) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ q ∈ K,
      ‖actualTransportDensityMultiplier σ η τ ξ q‖ ≤ C ∧
      ‖fderiv ℝ (actualTransportDensityMultiplier σ η τ ξ) q‖ ≤ C ∧
      ‖fderiv ℝ (regularJointMap (actualPhysicalCoordinate η τ ξ)) q‖ ≤ C := by
  have hm (q) (hq : q ∈ K) := actualTransportDensityMultiplier_interior_smooth hN σ hσ η τ ξ
    hη hτ hξ q (hupper q hq)
  have hr (q) (hq : q ∈ K) := actual_regular_map_interior_smooth η τ ξ hη hτ hξ q (hupper q hq)
  obtain ⟨C₀, h₀⟩ := hK.exists_bound_of_continuousOn (fun q hq => (hm q hq).continuousAt.continuousWithinAt)
  obtain ⟨C₁, h₁⟩ := hK.exists_bound_of_continuousOn (f := fderiv ℝ (actualTransportDensityMultiplier σ η τ ξ))
    (fun q hq => ((hm q hq).fderiv_right (m := 0) (by simp)).continuousAt.continuousWithinAt)
  obtain ⟨C₂, h₂⟩ := hK.exists_bound_of_continuousOn
    (f := fderiv ℝ (regularJointMap (actualPhysicalCoordinate η τ ξ)))
    (fun q hq => ((hr q hq).fderiv_right (m := 0) (by simp)).continuousAt.continuousWithinAt)
  let C := max 1 (max C₀ (max C₁ C₂))
  refine ⟨C, le_max_left _ _, ?_⟩
  intro q hq
  exact ⟨(h₀ q hq).trans ((le_max_left _ _).trans (le_max_right _ _)),
    (h₁ q hq).trans ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))),
    (h₂ q hq).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))⟩

end
end IsingBulk.AnisoF002.Isotropic
