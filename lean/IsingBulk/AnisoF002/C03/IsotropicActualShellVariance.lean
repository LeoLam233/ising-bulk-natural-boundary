import IsingBulk.AnisoF002.C03.IsotropicActualInverseScale
import IsingBulk.AnisoF002.C03.IsotropicActualCovarianceJets

/-!
# Actual inverse-difference sizes and shell variance coercivity

The fixed smallness choice uses the constructed smooth bumps. Both
the upper pair bound and the lower bilinear variance concern the full
population-dependent constrained deformation.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric

theorem exists_actual_shell_variance_control (η : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (N : ℕ), 0 < N →
      ∀ τ ∈ Icc 0 δ, ∀ ξ ∈ Icc 0 1, ∀ θ : Fin N → ℝ,
        (∀ i j, ‖actualHomotopyAngle η τ ξ θ i - actualHomotopyAngle η τ ξ θ j‖ ≤
          2 * |θ i - θ j|) ∧
        ∀ r : ℝ, 0 < r → (∃ i j, r ≤ |θ i - θ j|) →
          r ^ 2 / 4 ≤ (pairVariance (actualHomotopyAngle η τ ξ θ)).re := by
  obtain ⟨δV, hδV, hvar⟩ := exists_actual_variance_coercivity η
  obtain ⟨L, hL, _, _, hpL, hmL⟩ := actual_bump_global_first_bounds η
  let δ := min δV (1 / (4 * L))
  have hδ : 0 < δ := lt_min hδV (by positivity)
  have hδVle : δ ≤ δV := min_le_left _ _
  have hδL : δ * (4 * L) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 4 * L)).mp (min_le_right _ _)
  refine ⟨δ, hδ, ?_⟩
  intro N hN τ hτ ξ hξ θ
  have heff : 0 ≤ ξ * τ := mul_nonneg hξ.1 hτ.1
  have heffle : ξ * τ ≤ δ :=
    (show ξ * τ ≤ τ by nlinarith only [hξ.2, hτ.1]).trans hτ.2
  have heffL : (ξ * τ) * (L + L) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right heffle (by positivity : 0 ≤ 4 * L)
    nlinarith only [hh, hδL, mul_nonneg heff hL.le]
  refine ⟨?_, ?_⟩
  · intro i j
    let p := fun k : Fin N => upperPeriodicBump η (θ k)
    let m := fun k : Fin N => lowerPeriodicBump η (θ k)
    let h := balancedShift ((ξ * τ) / Fintype.card (Fin N)) p m
    have hshift : |h i - h j| ≤ ((ξ * τ) * (L + L)) * |θ i - θ j| :=
      balancedShift_pair_lipschitz θ p m (ξ * τ) L L (by simpa using hN) heff
        (fun k => upperPeriodicBump_bounds η (θ k)) (fun k => lowerPeriodicBump_bounds η (θ k))
        (fun k l => hpL (θ k) (θ l)) (fun k l => hmL (θ k) (θ l)) i j
    have hshift' : |h i - h j| ≤ |θ i - θ j| := hshift.trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right heffL (abs_nonneg (θ i - θ j)))
    have he : actualHomotopyAngle η τ ξ θ i - actualHomotopyAngle η τ ξ θ j =
        ((θ i - θ j : ℝ) : ℂ) - Complex.I * ((h i - h j : ℝ) : ℂ) := by
      have hscale : ξ * (τ / (Fintype.card (Fin N) : ℝ)) = (ξ * τ) / Fintype.card (Fin N) := by ring
      simp only [actualHomotopyAngle, balancedHomotopyCoordinate, contourCoordinate, hscale]
      dsimp only [h, p, m]
      push_cast
      ring
    rw [he]
    apply (norm_sub_le _ _).trans
    simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    linarith only [hshift']
  · intro r hr ⟨i, j, hij⟩
    have hc := hvar N hN τ ⟨hτ.1, hτ.2.trans hδVle⟩ ξ hξ θ
    have hp := selected_pair_le_realPairEnergy θ i j
    have hs : r ^ 2 ≤ (θ i - θ j) ^ 2 := by
      have hh := (sq_le_sq₀ hr.le (abs_nonneg (θ i - θ j))).mpr hij
      simpa only [sq_abs] using hh
    nlinarith only [hc, hp, hs]

end IsingBulk.AnisoF002.Isotropic
