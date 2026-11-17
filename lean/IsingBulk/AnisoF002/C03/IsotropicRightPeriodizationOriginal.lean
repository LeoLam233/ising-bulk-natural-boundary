import IsingBulk.AnisoF002.C03.IsotropicRightPeriodizationIntegral

/-!
# The original full-period box and every compact right mean

The original box [0,2 pi] is transferred exactly to the centered box by
its genuine constrained torus periodicity. Together with compact
periodization this identifies the actual complete particle integral,
including all original normalization, with all centered compact lifts.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set MeasureTheory
open IsingBulk.AnisoF002.RegularTail.C03
open IsingBulk.AnisoF002.NegativeHT

/-- Simultaneous integer shifts in the independent angles induce the
opposite full integer sum in the eliminated angle. -/
theorem affineConstraintAngles_toroidal_c03 {n : ℕ} (a : ℝ) (k : Fin n → ℤ) (x : Fin n → ℝ) :
    affineConstraintAngles a (toroidalTranslation k x) =
      toroidalTranslation (Fin.snoc k (-∑ i, k i)) (affineConstraintAngles a x) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [affineConstraintAngles_eq_snoc, Fin.snoc_last, toroidalTranslation,
      Finset.sum_add_distrib, Int.cast_neg, Int.cast_sum]
    rw [← Finset.sum_mul]
    ring
  · simp only [affineConstraintAngles_eq_snoc, Fin.snoc_castSucc, toroidalTranslation]

theorem rightCutoffProduct_toroidal {N : ℕ} (b δ ρ : ℝ) (k : Fin N → ℤ) (θ : Fin N → ℝ) :
    rightCutoffProduct b δ ρ N (toroidalTranslation k θ) = rightCutoffProduct b δ ρ N θ := by
  unfold rightCutoffProduct
  apply Finset.prod_congr rfl
  intro i _
  change (periodicRightCutoff b δ ρ (θ i + (k i : ℝ) * (2 * Real.pi)) : ℂ) = _
  rw [(periodicRightCutoff_periodic b δ ρ).int_mul (k i) (θ i)]

theorem angularIntegrationBox_eq_centered_integral {n : ℕ} (F : (Fin n → ℝ) → ℂ)
    (hF : ∀ k θ, F (toroidalTranslation k θ) = F θ) :
    (∫ x in angularIntegrationBox n, F x) = ∫ x in regularAngularBox n, F x := by
  have hz : windingPeriodBox n (fun _ => 0) =ᵐ[volume] angularIntegrationBox n := by
    change (Set.univ.pi fun _ : Fin n => Ioc (0 : ℝ) (0 + 2 * Real.pi)) =ᵐ[volume]
      Icc (fun _ : Fin n => (0 : ℝ)) (fun _ => 2 * Real.pi)
    rw [volume_pi]
    simpa only [zero_add] using
      (Measure.univ_pi_Ioc_ae_eq_Icc (μ := fun _ : Fin n => (volume : Measure ℝ))
        (f := fun _ => 0) (g := fun _ => 2 * Real.pi))
  rw [← setIntegral_congr_set hz, ← setIntegral_congr_set (windingPeriodBox_centered_ae n)]
  exact windingPeriodBox_integral_eq n F hF _ _

/-- Exact generic right periodization from the original full-period
independent box. -/
theorem original_rightProduct_integral_centered_lifts {b δ ρ β : ℝ} (h : RightCutoffGeometry b δ ρ)
    (hδ : δ ≤ β) (hρ : ρ + δ / 2 ≤ β) {n : ℕ}
    (F : (Fin (n + 1) → ℝ) → ℂ) (hc : Continuous F)
    (hF : ∀ k θ, F (toroidalTranslation k θ) = F θ) (a : ℝ) :
    (∫ x in angularIntegrationBox n,
      rightCutoffProduct b δ ρ (n + 1) (affineConstraintAngles a x) * F (affineConstraintAngles a x)) =
      ∑ l ∈ admissibleRightLifts (n + 1) b β a,
        ∫ x : Fin n → ℝ,
          compactRightProduct b δ ρ (n + 1)
            (centeredConstraintAngles (constrainedRightMean (n + 1) b a l - b) x) *
          F (centeredConstraintAngles (constrainedRightMean (n + 1) b a l - b) x) := by
  rw [angularIntegrationBox_eq_centered_integral]
  · exact rightProduct_integral_centered_lifts h hδ hρ F hc hF a
  · intro k x
    rw [affineConstraintAngles_toroidal_c03, rightCutoffProduct_toroidal, hF]

/-- The complete actual normalized right density on the original
angular box is exactly the finite sum of compact mean integrals. -/
theorem actual_original_right_density_integral_centered_lifts {b δ ρ β : ℝ}
    (h : RightCutoffGeometry b δ ρ) (hδ : δ ≤ β) (hρ : ρ + δ / 2 ≤ β)
    {n : ℕ} (s σ : ℂ) (hs : 0 < s.im) (hσ : ‖σ‖ ≤ 1)
    (η τ ξ : ℝ) (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ) (a : ℝ) :
    (∫ x in angularIntegrationBox n,
      actualLowerRightCutoff η b δ ρ (n + 1) (affineConstraintAngles a x) *
        homotopyPulledDensity η τ (isotropicBarePhysicalDensity s σ) (ξ, affineConstraintAngles a x)) =
      ∑ l ∈ admissibleRightLifts (n + 1) b β a,
        ∫ x : Fin n → ℝ,
          actualLowerCompactRightCutoff η b δ ρ (n + 1)
            (centeredConstraintAngles (constrainedRightMean (n + 1) b a l - b) x) *
          homotopyPulledDensity η τ (isotropicBarePhysicalDensity s σ)
            (ξ, centeredConstraintAngles (constrainedRightMean (n + 1) b a l - b) x) := by
  rw [angularIntegrationBox_eq_centered_integral]
  · exact actual_right_density_integral_centered_lifts h hδ hρ s σ hs hσ η τ ξ hη hτ hξ a
  · intro k x
    rw [affineConstraintAngles_toroidal_c03]
    simp only [actualLowerRightCutoff, lowerPopulationCutoff_toroidal, rightCutoffProduct_toroidal,
      homotopyPulledDensity_toroidal η τ ξ _ (isotropicBarePhysicalDensity_periodic s σ)]

end IsingBulk.AnisoF002.Isotropic
