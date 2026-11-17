import IsingBulk.AnisoF002.C03.IsotropicActualCurrent

/-!
# One actual neighborhood for the physical covariance current

The radius is chosen before N. Every full population-dependent right
homotopy in it, including endpoint slivers and proper partial diagonals,
has the actual smooth tangent velocity and exact scalar current.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric Filter

theorem exists_actual_oneSided_inverse_data (S : ℝ) (hS : 0 < S ∧ S < 2) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (N : ℕ), 0 < N → ∀ (s : ℂ), 0 < s.im → dist s (S : ℂ) < δ →
      ∀ (η τ ξ : ℝ), 0 < η → τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
      ∀ θ : Fin N → ℝ, (∀ i, θ i ∈ Icc (-Real.pi - δ) δ) → ∀ i,
        AnalyticAt ℂ explicitRightInverse (s, actualPhysicalCoordinate η τ ξ i (s, θ)) ∧
        Complex.cos (actualPhysicalCoordinate η τ ξ i (s, θ) / 2) ≠ 0 ∧
        explicitRightDenominator (s, actualPhysicalCoordinate η τ ξ i (s, θ)) ≠ 0 ∧
        explicitRightInverse (s, actualPhysicalCoordinate η τ ξ i (s, θ)) =
          actualHomotopyAngle η τ ξ θ i := by
  obtain ⟨r, hr, hU, hdata, _⟩ := exists_oneSided_inverse_protected_neighborhood S hS
  obtain ⟨δ, hδ, himage⟩ := exists_actual_oneSided_homotopy_domain S r hS hr
  refine ⟨δ, hδ, ?_⟩
  intro N hN s hs hsnear η τ ξ hη hτ hξ θ hθ i
  obtain ⟨hq, heq⟩ := himage N hN s hs hsnear η τ ξ hη hτ hξ θ hθ
  have hm : (s, actualPhysicalCoordinate η τ ξ i (s, θ)) ∈
      cthickening r (oneSidedParameterArc S) :=
    thickening_subset_cthickening r _ (oneSidedSingle_of_thickening hq.1 (hq.2 i))
  exact ⟨hU _ hm, (hdata _ hm).2.1, (hdata _ hm).2.2, heq i⟩

/-- Every regularity and tangency hypothesis of the current is derived
on the actual physical homotopy. No restriction is imposed on the
occupancy fractions or on any proper partial diagonal. -/
theorem exists_actual_right_current_data (S η : ℝ)
    (hS : 0 < S ∧ S < 2) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (N : ℕ), 0 < N → ∀ (s : ℂ), 0 < s.im → dist s (S : ℂ) < δ →
      ∀ τ ∈ Icc 0 δ, ∀ ξ ∈ Icc 0 1, ∀ θ : Fin N → ℝ,
        (∀ k, θ k ∈ Icc (-rightBranchEndpoint S - δ) δ) →
        ∀ i j, θ i ≠ θ j →
        (∀ k, ContDiffAt ℝ 2 (actualPhysicalCoordinate η τ ξ k) (s, θ)) ∧
        actualCoordinateDeterminant η τ ξ (s, θ) ≠ 0 ∧
        (∀ k, DifferentiableAt ℝ (actualCovarianceRegularField η τ ξ k) (s, θ)) ∧
        (∀ k, DifferentiableAt ℝ (actualCovarianceAngularVelocity η τ ξ k) (s, θ)) ∧
        (∑ k, actualCovarianceAngularVelocity η τ ξ k (s, θ)) = 0 := by
  obtain ⟨δ₁, hδ₁, hdensity⟩ := exists_actual_oneSided_scalar_density S η hS hη
  obtain ⟨δ₂, hδ₂, hcovariance⟩ := exists_actual_right_covariance_transport S η hS hη
  obtain ⟨δ₃, hδ₃, hinverse⟩ := exists_actual_oneSided_inverse_data S hS
  let δ := min δ₁ (min δ₂ δ₃)
  have hδ : 0 < δ := lt_min hδ₁ (lt_min hδ₂ hδ₃)
  have hd1 : δ ≤ δ₁ := min_le_left _ _
  have hd2 : δ ≤ δ₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hd3 : δ ≤ δ₃ := (min_le_right _ _).trans (min_le_right _ _)
  have hb := (rightBranchEndpoint_lt_pi S hS.1).le
  refine ⟨δ, hδ, ?_⟩
  intro N hN s hs hsnear τ hτ ξ hξ θ hθ i j hij
  have hθ1 : ∀ k, θ k ∈ Icc (-Real.pi - δ₁) δ₁ :=
    fun k => ⟨by linarith [(hθ k).1], (hθ k).2.trans hd1⟩
  have hθ2 : ∀ k, θ k ∈ Icc (-rightBranchEndpoint S - δ₂) δ₂ :=
    fun k => ⟨by linarith [(hθ k).1], (hθ k).2.trans hd2⟩
  have hθ3 : ∀ k, θ k ∈ Icc (-Real.pi - δ₃) δ₃ :=
    fun k => ⟨by linarith [(hθ k).1], (hθ k).2.trans hd3⟩
  obtain ⟨hχ, hdet, _⟩ := hdensity N hN s hs (hsnear.trans_le hd1) τ
    ⟨hτ.1, hτ.2.trans hd1⟩ ξ hξ θ hθ1
  obtain ⟨hB, _, hw, _, _⟩ := hcovariance N hN s hs (hsnear.trans_le hd2) τ
    ⟨hτ.1, hτ.2.trans hd2⟩ ξ hξ θ hθ2 i j hij
  have hdata := hinverse N hN s hs (hsnear.trans_le hd3) η τ ξ hη
    ⟨hτ.1, hτ.2.trans hd3⟩ hξ θ hθ3
  have hsheet (k : Fin N) : 0 < (isotropicDispersion (s, actualHomotopyAngle η τ ξ θ k)).im :=
    actual_balanced_homotopy_sheet s hs η τ ξ hη hτ.1 hξ.1 θ k
  have hBd := actualCovarianceRegularField_differentiableAt η τ ξ (s, θ) hχ hB
  have hVd := constructedAngularVelocity_differentiableAt
    (actualPhysicalCoordinate η τ ξ) actualAngularDirection actualTimeDirection (s, θ)
    (actualCovarianceRegularField η τ ξ) hχ hBd hdet
  have hV := actualCovarianceAngularVelocity_balanced η τ ξ (s, θ) hsheet hdet hdata
  refine ⟨hχ, hdet, hBd, hVd, ?_⟩
  exact rightCovarianceField_angular_tangent s
    (fun k => actualPhysicalCoordinate η τ ξ k (s, θ)) hw _
    (fun k => upperPeriodicBump η (θ k)) (fun k => lowerPeriodicBump η (θ k))
    (fun k => deriv (upperPeriodicBump η) (θ k))
    (fun k => deriv (lowerPeriodicBump η) (θ k))
    (fun k => actualCovarianceAngularVelocity η τ ξ k (s, θ)) hV

/-- The physical covariance current of frozen F002, on a common actual
right neighborhood. It applies also to smooth real cutoffs and every
differentiable parameter-dependent descendant amplitude. -/
theorem exists_actual_right_scalar_current (S η : ℝ)
    (hS : 0 < S ∧ S < 2) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (N : ℕ), 0 < N → ∀ (s : ℂ), 0 < s.im → dist s (S : ℂ) < δ →
      ∀ τ ∈ Icc 0 δ, ∀ ξ ∈ Icc 0 1, ∀ θ : Fin N → ℝ,
        (∀ k, θ k ∈ Icc (-rightBranchEndpoint S - δ) δ) →
        ∀ i j, θ i ≠ θ j →
        actualCoordinateDeterminant η τ ξ (s, θ) ≠ 0 ∧
        (∑ k, actualCovarianceAngularVelocity η τ ξ k (s, θ)) = 0 ∧
        ∀ b : (ℂ × (Fin N → ℝ)) → ℂ, DifferentiableAt ℝ b (s, θ) →
          scalarPartial (fun y => actualCoordinateDeterminant η τ ξ y * b y)
              actualTimeDirection (s, θ) -
            (∑ k, scalarPartial (fun y => actualCovarianceAngularVelocity η τ ξ k y *
              actualCoordinateDeterminant η τ ξ y * b y) (actualAngularDirection k) (s, θ)) =
          actualCoordinateDeterminant η τ ξ (s, θ) *
            (scalarRegularParameterDerivative (actualPhysicalCoordinate η τ ξ)
                actualAngularDirection actualTimeDirection b (s, θ) +
              (∑ k, actualCovarianceRegularField η τ ξ k (s, θ) *
                scalarRegularFrameDerivative (actualPhysicalCoordinate η τ ξ)
                  actualAngularDirection b k (s, θ)) +
              (∑ k, scalarRegularFrameDerivative (actualPhysicalCoordinate η τ ξ)
                actualAngularDirection (actualCovarianceRegularField η τ ξ k) k (s, θ)) * b (s, θ)) := by
  obtain ⟨δ, hδ, hdata⟩ := exists_actual_right_current_data S η hS hη
  refine ⟨δ, hδ, ?_⟩
  intro N hN s hs hsnear τ hτ ξ hξ θ hθ i j hij
  obtain ⟨hχ, hdet, hB, _, htangent⟩ := hdata N hN s hs hsnear τ hτ ξ hξ θ hθ i j hij
  refine ⟨hdet, htangent, ?_⟩
  intro b hb
  exact exact_constructed_regular_current (actualPhysicalCoordinate η τ ξ)
    actualAngularDirection actualTimeDirection (s, θ) (actualCovarianceRegularField η τ ξ) b hχ hB hb hdet

end IsingBulk.AnisoF002.Isotropic
