import IsingBulk.AnisoF002.C03.IsotropicInverseScalePrimitives

/-!
# The sharp inverse-coordinate derivative on every actual right shell

The second frozen coordinate-scale estimate is proved from the actual
P=0/P>0 population alternatives. The inverse is the already identified
physical inverse; its derivative is not a supplied scale hypothesis.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric

theorem inverse_coordinate_slope_physical (s w : ℂ)
    (hU : AnalyticAt ℂ explicitRightInverse (s, physicalRegularCoordinate (s, w)))
    (hc : Complex.cos (physicalRegularCoordinate (s, w) / 2) ≠ 0)
    (hD : explicitRightDenominator (s, physicalRegularCoordinate (s, w)) ≠ 0)
    (heq : explicitRightInverse (s, physicalRegularCoordinate (s, w)) = w) :
    deriv (fun z => explicitRightInverse (s, z)) (physicalRegularCoordinate (s, w)) =
      Complex.sin (upperPhysicalPhase (isotropicDispersion (s, w))) /
        explicitRightDenominator (s, physicalRegularCoordinate (s, w)) := by
  rw [← explicitRightCoordinateSlope_eq_deriv _ hU hc hD]
  unfold explicitRightCoordinateSlope
  rw [heq]
  have hφ : physicalRegularCoordinate (s, w) - w = upperPhysicalPhase (isotropicDispersion (s, w)) := by
    unfold physicalRegularCoordinate
    ring
  rw [hφ]

/-- The second estimate in frozen F002 `eq:iso-coordinate-scales`, on
the actual right support. Constants precede N and every shell. The
positive-population case is retained without any lower population bound. -/
theorem exists_actual_right_shell_inverse_coordinate_scale (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧
      ∀ (N : ℕ), 0 < N → ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      ∀ η τ ξ : ℝ, 0 < η → τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
      ∀ θ : Fin N → ℝ, (∀ i, θ i ∈ Icc (-b - δ) δ) →
      ∀ r : ℝ, 0 < r → (∀ i j, |θ i - θ j| ≤ 2 * r) →
      ∀ i : Fin N,
        ‖deriv (fun z => explicitRightInverse (isotropicRadialParameter α ε, z))
          ((actualHomotopyRegularTuple (isotropicRadialParameter α ε) η τ ξ θ).2 i)‖ ≤
            C * Real.sqrt (|angularMean (fun k => θ k + b)| + r + ε) := by
  have hcoslo := Real.cos_lt_cos_of_nonneg_of_le_pi hb.1.le le_rfl hb.2
  have hcoshi := Real.cos_lt_cos_of_nonneg_of_le_pi (show (0 : ℝ) ≤ 0 by norm_num) hb.2.le hb.1
  rw [Real.cos_pi] at hcoslo
  rw [Real.cos_zero] at hcoshi
  have hS : 0 < 2 * Real.cos α ∧ 2 * Real.cos α < 2 := by
    constructor <;> linarith only [hpoint, hcoslo, hcoshi]
  obtain ⟨δI, CI, hδI, hCI, hInv⟩ := exists_actual_oneSided_inverse_slope_bounds (2 * Real.cos α) hS
  obtain ⟨R, _, CB, hR, _, _, hCB, hbranch⟩ := exists_isotropic_branch_sine_bounds α b hα hb hpoint
  let δ := min 1 (min R (min (δI / 8) ((Real.pi - b) / 2)))
  have hδ : 0 < δ := lt_min zero_lt_one (lt_min hR (lt_min (by positivity) (by linarith only [hb.2])))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδR : δ ≤ R := (min_le_right _ _).trans (min_le_left _ _)
  have hδI8 : δ ≤ δI / 8 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδedge : δ ≤ (Real.pi - b) / 2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδIle : δ ≤ δI := by linarith only [hδI8, hδI]
  let C₁ := 2 * CB * CI
  let C₂ := 2 * CI / Real.sqrt R
  let C₃ := CI / Real.sqrt (b / 2)
  let C := C₁ + C₂ + C₃
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR
  have hsb : 0 < Real.sqrt (b / 2) := Real.sqrt_pos.mpr (div_pos hb.1 (by norm_num))
  have hC₁ : 0 < C₁ := by dsimp [C₁]; positivity
  have hC₂ : 0 < C₂ := by dsimp [C₂]; positivity
  have hC₃ : 0 < C₃ := by dsimp [C₃]; positivity
  have hC₁le : C₁ ≤ C := by dsimp [C]; linarith only [hC₂, hC₃]
  have hC₂le : C₂ ≤ C := by dsimp [C]; linarith only [hC₁, hC₃]
  have hC₃le : C₃ ≤ C := by dsimp [C]; linarith only [hC₁, hC₂]
  refine ⟨δ, C, hδ, hδ1, hC₁.trans_le hC₁le, ?_⟩
  intro N hN ε hε hεδ η τ ξ hη hτ hξ θ hθ r hr hdiam i
  let s := isotropicRadialParameter α ε
  let v := (actualHomotopyRegularTuple s η τ ξ θ).2 i
  let T := |angularMean (fun k => θ k + b)| + r + ε
  have hT : 0 < T := by dsimp [T]; positivity
  have hrad := isotropicRadialParameter_estimates α ε hα hε (hεδ.trans hδ1)
  have hsnear : dist s ((2 * Real.cos α : ℝ) : ℂ) < δI :=
    hrad.2.2.2.2.trans_lt (by linarith only [hεδ, hδI8, hδI])
  have hθI : ∀ k, θ k ∈ Icc (-Real.pi - δI) δI := by
    intro k
    exact ⟨by linarith only [(hθ k).1, hb.2, hδIle], (hθ k).2.trans hδIle⟩
  have hθpi : ∀ k, -Real.pi ≤ θ k := by
    intro k
    linarith only [(hθ k).1, hδedge, hb.2]
  obtain ⟨hU, hc, hD, heq, hUv, hDen⟩ := hInv N hN s hrad.2.2.2.1 hsnear
    η τ ξ hη ⟨hτ.1, hτ.2.trans hδIle⟩ hξ θ hθI i
  have hsqrt := actual_angular_sqrt_scale_bound hN b ε r hε.le hr.le θ hdiam i
  change ‖deriv (fun z => explicitRightInverse (s, z)) v‖ ≤ C * Real.sqrt T
  by_cases hP : actualUpperOccupancy η θ = 0
  · by_cases hlocal : |θ i + b| ≤ R
    · have hangle := actualHomotopyAngle_of_upperPopulation_zero hN η τ ξ θ hP i
      have hslope : deriv (fun z => explicitRightInverse (s, z)) v =
          Complex.sin (upperPhysicalPhase (isotropicDispersion (s, (θ i : ℂ)))) /
            explicitRightDenominator (s, v) := by
        have hh := inverse_coordinate_slope_physical s (actualHomotopyAngle η τ ξ θ i) hU hc hD heq
        change deriv (fun z => explicitRightInverse (s, z)) v =
          Complex.sin (upperPhysicalPhase (isotropicDispersion (s, actualHomotopyAngle η τ ξ θ i))) /
            explicitRightDenominator (s, v) at hh
        rwa [hangle] at hh
      have hdisp : isotropicBranchDispersion α b ε (θ i + b) 0 =
          isotropicDispersion (s, (θ i : ℂ)) := by
        simp only [isotropicBranchDispersion, s, Complex.ofReal_zero, mul_zero, sub_zero,
          show -b + (θ i + b) = θ i by ring]
      have hsin := (hbranch ε hε (hεδ.trans hδR) (θ i + b) 0 hlocal ⟨le_rfl, hR.le⟩).2
      rw [hdisp, add_zero] at hsin
      rw [hslope, norm_div, div_eq_mul_inv]
      have hDen' : ‖explicitRightDenominator (s, v)‖⁻¹ ≤ CI := by simpa only [norm_inv] using hDen
      calc
        _ ≤ (CB * Real.sqrt (|θ i + b| + ε)) * CI :=
          mul_le_mul hsin hDen' (inv_nonneg.mpr (norm_nonneg _)) (by positivity)
        _ ≤ (CB * (2 * Real.sqrt T)) * CI := by gcongr
        _ = C₁ * Real.sqrt T := by dsimp [C₁]; ring
        _ ≤ C * Real.sqrt T := mul_le_mul_of_nonneg_right hC₁le (Real.sqrt_nonneg _)
    · have hRle : Real.sqrt R ≤ 2 * Real.sqrt T :=
        (Real.sqrt_le_sqrt (show R ≤ |θ i + b| + ε by linarith only [lt_of_not_ge hlocal, hε])).trans hsqrt
      have hbound : CI ≤ C₂ * Real.sqrt T := by
        dsimp [C₂]
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ hsR).mpr
        have hh := mul_le_mul_of_nonneg_left hRle hCI.le
        nlinarith only [hh]
      exact hUv.trans (hbound.trans (mul_le_mul_of_nonneg_right hC₂le (Real.sqrt_nonneg _)))
  · have hPpos : 0 < actualUpperOccupancy η θ := by
      have hp0 := (actualUpperOccupancy_mem_Icc hN η θ).1
      rcases lt_or_eq_of_le hp0 with hh | hh
      · exact hh
      · exact False.elim (hP hh.symm)
    have hlow : b / 2 ≤ T := actual_upperPopulation_pos_scale_lower hN b η ε r hη hε.le θ hθpi hdiam hPpos
    have hroot : Real.sqrt (b / 2) ≤ Real.sqrt T := Real.sqrt_le_sqrt hlow
    have hbound : CI ≤ C₃ * Real.sqrt T := by
      dsimp [C₃]
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hsb).mpr
      exact mul_le_mul_of_nonneg_left hroot hCI.le
    exact hUv.trans (hbound.trans (mul_le_mul_of_nonneg_right hC₃le (Real.sqrt_nonneg _)))

end IsingBulk.AnisoF002.Isotropic
