import IsingBulk.AnisoF002.C03.IsotropicActualOccupancyPhase

/-!
# Uniform control of the full occupancy correction

The correction contains both differentiated full populations. Its
extreme-coordinate difference has the required angular gap factor;
the normalization cancels N exactly, before any coarea estimate.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric

theorem actualOccupancyPhaseCorrection_sub {N : ℕ} (s : ℂ) (η τ ξ : ℝ)
    (θ : Fin N → ℝ) (i j : Fin N) :
    actualOccupancyPhaseCorrection s η τ ξ θ i - actualOccupancyPhaseCorrection s η τ ξ θ j =
      -Complex.I * (((ξ * τ) / (N : ℝ) : ℝ) : ℂ) *
        ((deriv (upperPeriodicBump η) (θ i) - deriv (upperPeriodicBump η) (θ j) : ℝ) : ℂ) *
          actualLowerPhasePopulation s η τ ξ θ +
      Complex.I * (((ξ * τ) / (N : ℝ) : ℝ) : ℂ) *
        ((deriv (lowerPeriodicBump η) (θ i) - deriv (lowerPeriodicBump η) (θ j) : ℝ) : ℂ) *
          actualUpperPhasePopulation s η τ ξ θ := by
  unfold actualOccupancyPhaseCorrection
  push_cast
  ring

/-- The entire correction in the constrained extreme derivative costs
O(tau times angular gap times the full phase-slope envelope), uniformly
before particle number. Both global populations are present. -/
theorem exists_actual_occupancy_correction_difference_bound (η : ℝ) :
    ∃ L : ℝ, 0 < L ∧ ∀ (N : ℕ), 0 < N →
      ∀ (s : ℂ) (τ ξ : ℝ), 0 ≤ τ → 0 ≤ ξ →
      ∀ (θ : Fin N → ℝ) (Q : ℝ), 0 ≤ Q →
        (∀ k, ‖actualPhaseSlope s η τ ξ θ k‖ ≤ Q) →
      ∀ i j : Fin N,
        ‖actualOccupancyPhaseCorrection s η τ ξ θ i - actualOccupancyPhaseCorrection s η τ ξ θ j‖ ≤
          (ξ * τ) * L * Q * |θ i - θ j| := by
  obtain ⟨L, hL, hpL, hmL⟩ := actual_bump_derivative_lipschitz η
  refine ⟨2 * L, by positivity, ?_⟩
  intro N hN s τ ξ hτ hξ θ Q hQ hψ i j
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hscale : 0 ≤ (ξ * τ) / (N : ℝ) := div_nonneg (mul_nonneg hξ hτ) hn.le
  obtain ⟨hBm, hBp⟩ := actualPhasePopulation_norm_bounds s η τ ξ Q θ hψ
  have hp := hpL (θ i) (θ j)
  have hm := hmL (θ i) (θ j)
  rw [actualOccupancyPhaseCorrection_sub]
  apply (norm_add_le _ _).trans
  simp only [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hscale]
  have h₁ : ((ξ * τ) / (N : ℝ)) *
      |deriv (upperPeriodicBump η) (θ i) - deriv (upperPeriodicBump η) (θ j)| *
        ‖actualLowerPhasePopulation s η τ ξ θ‖ ≤
      ((ξ * τ) / (N : ℝ)) * (L * |θ i - θ j|) * ((N : ℝ) * Q) := by gcongr
  have h₂ : ((ξ * τ) / (N : ℝ)) *
      |deriv (lowerPeriodicBump η) (θ i) - deriv (lowerPeriodicBump η) (θ j)| *
        ‖actualUpperPhasePopulation s η τ ξ θ‖ ≤
      ((ξ * τ) / (N : ℝ)) * (L * |θ i - θ j|) * ((N : ℝ) * Q) := by gcongr
  calc
    _ ≤ 2 * (((ξ * τ) / (N : ℝ)) * (L * |θ i - θ j|) * ((N : ℝ) * Q)) := by linarith only [h₁, h₂]
    _ = _ := by field_simp

def actualFullPhaseDerivative {N : ℕ} (s : ℂ) (η τ ξ : ℝ) (θ : Fin N → ℝ) (i : Fin N) : ℂ :=
  actualPhaseSlope s η τ ξ θ i *
      fixedOccupancySlope η (ξ * τ) (actualUpperOccupancy η θ) (actualLowerOccupancy η θ) (θ i) +
    actualOccupancyPhaseCorrection s η τ ξ θ i

def constrainedAngleLine {N : ℕ} (θ : Fin N → ℝ) (i j : Fin N) (t : ℝ) : Fin N → ℝ :=
  θ + t • (Pi.single i 1 - Pi.single j 1)

theorem constrainedAngleLine_sum {N : ℕ} (θ : Fin N → ℝ) (i j : Fin N) (t : ℝ) :
    ∑ k, constrainedAngleLine θ i j t k = ∑ k, θ k := by
  simp only [constrainedAngleLine, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_add_distrib, ← Finset.mul_sum, Pi.sub_apply, Finset.sum_sub_distrib]
  simp

/-- The derivative used by coarea is taken along the actual constrained
line. It is the difference of the complete physical coordinate derivatives,
so both population corrections are restored before projecting the phase. -/
theorem actualTotalPhase_constrainedLine_hasDerivAt {N : ℕ} (s : ℂ) (hs : 0 < s.im)
    (η τ ξ : ℝ) (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ)
    (θ : Fin N → ℝ) (i j : Fin N) :
    HasDerivAt (fun t : ℝ => actualTotalPhase η τ ξ (s, constrainedAngleLine θ i j t))
      (actualFullPhaseDerivative s η τ ξ θ i - actualFullPhaseDerivative s η τ ξ θ j) 0 := by
  let f : (Fin N → ℝ) → ℂ := fun y => actualTotalPhase η τ ξ (s, y)
  have hfull := actualTotalPhase_differentiableAt η τ ξ (s, θ)
    (fun k => actualPhysicalCoordinate_contDiffAt η τ ξ k (s, θ) 2
      (actual_balanced_homotopy_sheet s hs η τ ξ hη hτ hξ θ k))
  have hmap : DifferentiableAt ℝ (fun y : Fin N → ℝ => (s, y)) θ :=
    ((hasFDerivAt_const s θ).prodMk (hasFDerivAt_id θ)).differentiableAt
  have hf : DifferentiableAt ℝ f θ := hfull.comp θ hmap
  have hpath (a : Fin N → ℝ) : HasDerivAt (fun t : ℝ => θ + t • a) a 0 := by
    simpa only [one_smul, id_eq, zero_add] using!
      (hasDerivAt_const (0 : ℝ) θ).add ((hasDerivAt_id (0 : ℝ)).smul_const a)
  have hfAt : HasFDerivAt f (fderiv ℝ f θ) (θ + (0 : ℝ) • (Pi.single i 1 - Pi.single j 1)) := by
    simpa only [zero_smul, add_zero] using hf.hasFDerivAt
  have hmain := hfAt.comp_hasDerivAt 0 (hpath (Pi.single i 1 - Pi.single j 1))
  have hpartial (k : Fin N) : fderiv ℝ f θ (Pi.single k 1) = actualFullPhaseDerivative s η τ ξ θ k := by
    have hdAt : HasFDerivAt f (fderiv ℝ f θ) (θ + (0 : ℝ) • Pi.single k 1) := by
      simpa only [zero_smul, add_zero] using hf.hasFDerivAt
    have hd := hdAt.comp_hasDerivAt 0 (hpath (Pi.single k 1))
    have he : (fun t : ℝ => f (θ + t • Pi.single k 1)) =
        (fun t : ℝ => actualTotalPhase η τ ξ (s, coordinateLine θ k t)) := by
      funext t
      congr 2
      funext l
      by_cases hl : l = k
      · subst l
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one,
          coordinateLine, ite_true]
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne hl, mul_zero,
          add_zero, coordinateLine, hl, ite_false]
    change HasDerivAt (fun t : ℝ => f (θ + t • Pi.single k 1)) _ 0 at hd
    rw [he] at hd
    exact hd.unique (actualTotalPhase_coordinateLine_hasDerivAt s hs η τ ξ hη hτ hξ θ k)
  change HasDerivAt (fun t : ℝ => actualTotalPhase η τ ξ (s, constrainedAngleLine θ i j t)) _ 0 at hmain
  rw [map_sub, hpartial i, hpartial j] at hmain
  exact hmain

end IsingBulk.AnisoF002.Isotropic
