import IsingBulk.AnisoF002.C03.IsotropicFirstSmoothLimit
import IsingBulk.AnisoF002.C03.IsotropicFirstPlateau

/-!
# Exact attachment of the nonzero smooth first chart to the physical partition

The full deformation and its determinant are the identity on the chosen
actual lower plateau. The literal near-coincidence coefficient therefore
equals the smooth first coefficient as a function of the original
temperature variable. Every ordinary complex jet and its leading limit
is attached by exact function equality.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter MeasureTheory IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology BigOperators

theorem centeredConstraintAngles_eq_flat {n : ℕ} (μ : ℝ) (q : Fin n → ℝ) :
    centeredConstraintAngles μ q = fun i => μ + flatConstrainedAngles q i := by
  have hh := centeredConstraintAngles_sub_const μ q
  rw [constrainedTangentMap_apply] at hh
  funext i
  have hi := congrFun hh i
  change centeredConstraintAngles μ q i - μ = flatConstrainedAngles q i at hi
  linarith

theorem exists_actual_first_near_coefficient_identity (n : ℕ) {α η b δB ρB : ℝ}
    (hα : 0 < α) (hπ : α < Real.pi) (hη : 0 < η)
    (hηα : 2 * η < Real.sin α) (hαb : α < b) (hcut : RightCutoffGeometry b δB ρB) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ → ∀ τ ξ : ℝ, ∀ σ : ℂ,
      centeredWeightedPhysicalCoefficient η τ ξ (-α) σ
          (weightedCollisionNear r (actualLowerCompactRightCutoff η b δB ρB (n + 1))) =
        fun S => isotropicFirstSmoothCoefficient n α σ r (S - (2 * Real.cos α : ℂ)) := by
  obtain ⟨R, hR, hplateau⟩ := exists_isotropic_first_actual_plateau n hα hπ hη hηα hαb hcut
  refine ⟨R / 4, by positivity, ?_⟩
  intro r hr hrR τ ξ σ
  funext S
  unfold centeredWeightedPhysicalCoefficient isotropicFirstSmoothCoefficient
  apply integral_congr_ae
  exact Eventually.of_forall fun q => by
    dsimp only
    rw [weightedCollisionNear, isotropicFirstShapeCutoff_centered]
    by_cases hq : isotropicFirstShapeCutoff r q = 0
    · rw [hq, mul_zero, zero_mul, zero_mul]
    · have hs := isotropicFirstShapeCutoff_support hr q hq
      have hqR : q ∈ isotropicFirstShapeBall n R := by
        change angularQuadratic (flatConstrainedAngles q) < R
        linarith
      have hp := hplateau q hqR τ ξ S σ
      rw [← centeredConstraintAngles_eq_flat] at hp
      calc
        _ = isotropicFirstShapeCutoff r q *
            (actualLowerCompactRightCutoff η b δB ρB (n + 1) (centeredConstraintAngles (-α) q) *
              homotopyPulledDensity η τ (isotropicBarePhysicalDensity S σ)
                (ξ, centeredConstraintAngles (-α) q)) := by ring
        _ = _ := by rw [hp]

theorem exists_actual_first_near_all_small_scaled_limits {n j l : ℕ} {α η b δB ρB : ℝ}
    (hα : 0 < α) (hhalf : α < Real.pi / 2) (hη : 0 < η)
    (hηα : 2 * η < Real.sin α) (hαb : α < b) (hcut : RightCutoffGeometry b δB ρB)
    (σ : ℂ) (hσ : ‖σ‖ ≤ 1)
    (hres : σ * Complex.exp (-(((n + 1 : ℕ) : ℂ) * ((α : ℂ) * Complex.I))) = 1)
    (hl : 0 < l) (hdegree : 2 * j + 2 = n + 2 * (n + 1).choose 2 + l) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ → ∀ τ ξ : ℝ,
      Tendsto (fun s : ℝ => (s : ℂ) ^ l *
        iteratedDeriv j (centeredWeightedPhysicalCoefficient η τ ξ (-α) σ
          (weightedCollisionNear r (actualLowerCompactRightCutoff η b δB ρB (n + 1))))
          (isotropicRadialParameter α (s ^ 2)))
        (𝓝[>] (0 : ℝ)) (𝓝 (isotropicFirstChartAmplitude n α j)) := by
  have hπ : α < Real.pi := hhalf.trans (by linarith [Real.pi_pos])
  obtain ⟨rA, hrA, heq⟩ := exists_actual_first_near_coefficient_identity n hα hπ hη hηα hαb hcut
  obtain ⟨rL, hrL, hlim⟩ := exists_isotropic_first_all_small_smooth_scaled_limits hα hhalf σ hσ hres hl hdegree
  refine ⟨min rA rL, lt_min hrA hrL, ?_⟩
  intro r hr hrle τ ξ
  rw [heq r hr (hrle.trans (min_le_left _ _)) τ ξ σ, iteratedDeriv_comp_sub_const]
  exact hlim r hr (hrle.trans (min_le_right _ _))

theorem exists_actual_first_odd_near_nonzero_limit {n : ℕ} (hn0 : 0 < n) (hn : Odd (n + 1))
    {α η b δB ρB : ℝ} (hα : 0 < α) (hhalf : α < Real.pi / 2) (hη : 0 < η)
    (hηα : 2 * η < Real.sin α) (hαb : α < b) (hcut : RightCutoffGeometry b δB ρB)
    (σ : ℂ) (hσ : ‖σ‖ ≤ 1)
    (hres : σ * Complex.exp (-(((n + 1 : ℕ) : ℂ) * ((α : ℂ) * Complex.I))) = 1) :
    isotropicFirstChartAmplitude n α (oddTopOrder (n + 1)) ≠ 0 ∧
      ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ → ∀ τ ξ : ℝ,
        Tendsto (fun s : ℝ => (s : ℂ) ^ 2 *
          iteratedDeriv (oddTopOrder (n + 1)) (centeredWeightedPhysicalCoefficient η τ ξ (-α) σ
            (weightedCollisionNear r (actualLowerCompactRightCutoff η b δB ρB (n + 1))))
            (isotropicRadialParameter α (s ^ 2)))
          (𝓝[>] (0 : ℝ)) (𝓝 (isotropicFirstChartAmplitude n α (oddTopOrder (n + 1)))) :=
  ⟨isotropicFirstChartAmplitude_odd_ne_zero hn0 hn hα hhalf,
    exists_actual_first_near_all_small_scaled_limits hα hhalf hη hηα hαb hcut σ hσ hres
      (by norm_num) (odd_first_scaling_degree hn)⟩

theorem exists_actual_first_even_near_nonzero_limit {n : ℕ} (hn : Even (n + 1))
    {α η b δB ρB : ℝ} (hα : 0 < α) (hhalf : α < Real.pi / 2) (hη : 0 < η)
    (hηα : 2 * η < Real.sin α) (hαb : α < b) (hcut : RightCutoffGeometry b δB ρB)
    (σ : ℂ) (hσ : ‖σ‖ ≤ 1)
    (hres : σ * Complex.exp (-(((n + 1 : ℕ) : ℂ) * ((α : ℂ) * Complex.I))) = 1) :
    isotropicFirstChartAmplitude n α (evenTopOrder (n + 1)) ≠ 0 ∧
      ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ → ∀ τ ξ : ℝ,
        Tendsto (fun s : ℝ => (s : ℂ) *
          iteratedDeriv (evenTopOrder (n + 1)) (centeredWeightedPhysicalCoefficient η τ ξ (-α) σ
            (weightedCollisionNear r (actualLowerCompactRightCutoff η b δB ρB (n + 1))))
            (isotropicRadialParameter α (s ^ 2)))
          (𝓝[>] (0 : ℝ)) (𝓝 (isotropicFirstChartAmplitude n α (evenTopOrder (n + 1)))) := by
  refine ⟨isotropicFirstChartAmplitude_even_ne_zero hn hα hhalf, ?_⟩
  simpa only [pow_one] using exists_actual_first_near_all_small_scaled_limits hα hhalf hη hηα hαb
    hcut σ hσ hres (by norm_num : 0 < 1) (even_first_scaling_degree hn)

end
end IsingBulk.AnisoF002.Isotropic
