import IsingBulk.AnisoF002.C03.IsotropicFirstSmallCharts
import IsingBulk.AnisoF002.C03.IsotropicCompactRightCutoff
import IsingBulk.AnisoF002.C03.IsotropicActualHomotopyCurrent

/-!
# Exact actual first chart inside the physical smooth partition

On the open lower plateau the actual upper bump and its differential
vanish.  Consequently the complete population-dependent deformation,
including its full determinant, is the identity.  A sufficiently small
fixed constrained quadratic chart about the first coincidence is inside
this plateau and the actual compact right cutoff is exactly one there.
The identities below are identities of the full physical density for
every complex parameter and signed kernel, not asymptotic replacements.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology BigOperators

theorem upperPeriodicBump_deriv_zero {η θ : ℝ} (hη : 0 < η)
    (hθ : Real.sin θ < η) : deriv (upperPeriodicBump η) θ = 0 := by
  have he : upperPeriodicBump η =ᶠ[𝓝 θ] (fun _ => 0) := by
    filter_upwards [Real.continuous_sin.continuousAt.eventually (Iio_mem_nhds hθ)] with x hx
    exact upperPeriodicBump_zero hη hx.le
  simpa only [deriv_const] using he.deriv_eq

theorem actualHomotopyAngle_lower_plateau {N : ℕ} {η : ℝ} (hη : 0 < η)
    (τ ξ : ℝ) (θ : Fin N → ℝ) (hθ : ∀ i, Real.sin (θ i) < η) :
    actualHomotopyAngle η τ ξ θ = complexAngles θ := by
  funext i
  rw [actualHomotopyAngle_affine_time]
  simp [actualHomotopyDisplacement, balancedShift,
    fun j => upperPeriodicBump_zero hη (hθ j).le, complexAngles]

theorem actualBalancedJacobian_lower_plateau {N : ℕ} {η : ℝ} (hη : 0 < η)
    (τ ξ : ℝ) (θ : Fin N → ℝ) (hθ : ∀ i, Real.sin (θ i) < η) :
    actualBalancedJacobian η τ ξ θ = LinearMap.id := by
  ext v i
  simp [actualBalancedJacobian, balancedAngularJacobian, balancedDisplacementDifferential,
    fun j => upperPeriodicBump_zero hη (hθ j).le,
    fun j => upperPeriodicBump_deriv_zero hη (hθ j)]

theorem homotopyPulledDensity_lower_plateau {N : ℕ} {η : ℝ} (hη : 0 < η)
    (τ ξ : ℝ) (F : (Fin N → ℂ) → ℂ) (θ : Fin N → ℝ)
    (hθ : ∀ i, Real.sin (θ i) < η) :
    homotopyPulledDensity η τ F (ξ, θ) = F (complexAngles θ) := by
  rw [homotopyPulledDensity_actual, actualBalancedJacobian_lower_plateau hη τ ξ θ hθ,
    actualHomotopyAngle_lower_plateau hη τ ξ θ hθ, LinearMap.det_id, one_mul]

theorem lowerPopulationCutoff_lower_plateau {N : ℕ} (hN : 0 < N)
    {η : ℝ} (hη : 0 < η) (θ : Fin N → ℝ)
    (hθ : ∀ i, Real.sin (θ i) ≤ -(2 * η)) : lowerPopulationCutoff η θ = 1 := by
  have hp (i : Fin N) : upperPeriodicBump η (θ i) = 0 :=
    upperPeriodicBump_zero hη (by linarith [hθ i])
  have hm (i : Fin N) : lowerPeriodicBump η (θ i) = 1 := by
    apply upperPeriodicBump_one hη
    rw [Real.sin_neg]
    linarith [hθ i]
  have hP : actualUpperPopulation η θ = 0 := by simp [actualUpperPopulation, hp]
  have hQ : actualLowerPopulation η θ = N := by simp [actualLowerPopulation, hm]
  have hNat : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [lowerPopulationCutoff, hP, hQ, populationTransition_zero (by norm_num),
    populationTransition_one (by linarith)]
  norm_num

theorem actualLowerCompactRightCutoff_lower_plateau {N : ℕ} (hN : 0 < N)
    {η b δ ρ : ℝ} (hη : 0 < η) (hg : RightCutoffGeometry b δ ρ)
    (θ : Fin N → ℝ) (hθ : ∀ i, Real.sin (θ i) ≤ -(2 * η))
    (hfund : ∀ i, θ i ∈ Icc (-Real.pi) Real.pi)
    (hcut : ∀ i, θ i ∈ Icc (-b - δ / 2) ρ) :
    actualLowerCompactRightCutoff η b δ ρ N θ = 1 := by
  have hc (i : Fin N) : compactRightCutoff b δ ρ (θ i) = 1 := by
    rw [compactRightCutoff_eq_periodic hg (hfund i), periodicRightCutoff_one hg (hcut i)]
  simp only [actualLowerCompactRightCutoff, lowerPopulationCutoff_lower_plateau hN hη θ hθ,
    Complex.ofReal_one, one_mul, compactRightProduct, hc, Finset.prod_const_one]

/-- The radius is selected after every actual partition parameter.  No
condition on the physical parameter, kernel, or deformation time is
needed for this exact local identification. -/
theorem exists_isotropic_first_actual_plateau (n : ℕ) {α η b δ ρ : ℝ}
    (hα : 0 < α) (hπ : α < Real.pi) (hη : 0 < η)
    (hηα : 2 * η < Real.sin α) (hαb : α < b)
    (hg : RightCutoffGeometry b δ ρ) :
    ∃ r : ℝ, 0 < r ∧ ∀ q : Fin n → ℝ, q ∈ isotropicFirstShapeBall n r →
      ∀ τ ξ : ℝ, ∀ S σ : ℂ,
        actualLowerCompactRightCutoff η b δ ρ (n + 1)
            (fun i => -α + flatConstrainedAngles q i) *
          homotopyPulledDensity η τ (isotropicBarePhysicalDensity S σ)
            (ξ, fun i => -α + flatConstrainedAngles q i) =
          isotropicFirstJointDensity α σ
            (S - (2 * Real.cos α : ℂ), complexAngles (flatConstrainedAngles q)) := by
  let U : Set ℝ := Ioo (-Real.pi) Real.pi ∩ Ioo (-b - δ / 2) ρ ∩
    {θ | Real.sin θ < -(2 * η)}
  have hU : IsOpen U :=
    (isOpen_Ioo.inter isOpen_Ioo).inter (isOpen_lt Real.continuous_sin continuous_const)
  have hc : -α ∈ U := by
    refine ⟨⟨⟨by linarith, by linarith [Real.pi_pos]⟩,
      ⟨by linarith [hg.delta_pos], by linarith [hg.rho_pos]⟩⟩, ?_⟩
    change Real.sin (-α) < -(2 * η)
    rw [Real.sin_neg]
    linarith
  have hev : ∀ᶠ q : Fin n → ℝ in 𝓝 0,
      ∀ i, -α + flatConstrainedAngles q i ∈ U := by
    apply Filter.eventually_all.mpr
    intro i
    have hh : ContinuousAt (fun q : Fin n → ℝ => -α + flatConstrainedAngles q i) 0 :=
      continuousAt_const.add (((continuous_apply i).comp
        (flatConstrainedAngles_continuous n)).continuousAt)
    have hz : -α + flatConstrainedAngles (0 : Fin n → ℝ) i = -α := by
      induction i using Fin.lastCases <;> simp [flatConstrainedAngles]
    apply hh.eventually
    change ∀ᶠ y : ℝ in 𝓝 (-α + flatConstrainedAngles (0 : Fin n → ℝ) i), y ∈ U
    rw [hz]
    exact hU.mem_nhds hc
  obtain ⟨d, hd, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨d ^ 2, sq_pos_of_pos hd, ?_⟩
  intro q hq τ ξ S σ
  have hqnorm : ‖q‖ < d := by
    have hlow := flatConstrainedAngles_quadratic_lower q
    change angularQuadratic (flatConstrainedAngles q) < d ^ 2 at hq
    nlinarith [norm_nonneg q]
  have hall := hball (by simpa only [dist_zero_right] using hqnorm)
  have hsin (i : Fin (n + 1)) : Real.sin (-α + flatConstrainedAngles q i) < η := by
    have hh := (hall i).2
    change Real.sin (-α + flatConstrainedAngles q i) < -(2 * η) at hh
    linarith
  rw [actualLowerCompactRightCutoff_lower_plateau (Nat.succ_pos n) hη hg _
    (fun i => (hall i).2.le) (fun i => Ioo_subset_Icc_self (hall i).1.1)
    (fun i => Ioo_subset_Icc_self (hall i).1.2), one_mul,
    homotopyPulledDensity_lower_plateau hη τ ξ _ _ hsin]
  unfold isotropicFirstJointDensity
  rw [add_sub_cancel]
  congr 1
  funext i
  simp only [complexAngles, Complex.ofReal_add, Complex.ofReal_neg]

end
end IsingBulk.AnisoF002.Isotropic
