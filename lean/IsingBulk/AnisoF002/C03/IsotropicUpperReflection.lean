import IsingBulk.AnisoF002.C03.IsotropicFullPhysicalHomotopy
import IsingBulk.AnisoF002.C03.RegularIsotropicPopulationSplit

/-!
# Exact reflection of the complete physical isotropic density

Reflection exchanges both actual bump populations. The full balanced
Jacobian is unchanged, every root and one-body factor is unchanged,
and each complete canceled pair is unchanged. The signed product
kernel and the original factorial/angular normalization are retained.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open IsingBulk.AnisoF002.RegularTail

theorem actual_bump_derivatives_reflection (η θ : ℝ) :
    deriv (upperPeriodicBump η) (-θ) = -deriv (lowerPeriodicBump η) θ ∧
      deriv (lowerPeriodicBump η) (-θ) = -deriv (upperPeriodicBump η) θ := by
  have hm (x : ℝ) : deriv (lowerPeriodicBump η) x = -deriv (upperPeriodicBump η) (-x) :=
    deriv_comp_neg (upperPeriodicBump η) x
  exact ⟨by rw [hm, neg_neg], by simpa only [neg_neg] using hm (-θ)⟩

theorem actualHomotopyDisplacement_reflection {ι : Type*} [Fintype ι]
    (η τ : ℝ) (θ : ι → ℝ) :
    actualHomotopyDisplacement η τ (fun i => -θ i) =
      fun i => -actualHomotopyDisplacement η τ θ i := by
  funext i
  simp only [actualHomotopyDisplacement, balancedShift, lowerPeriodicBump, neg_neg]
  ring

theorem actualHomotopyAngle_reflection {ι : Type*} [Fintype ι]
    (η τ ξ : ℝ) (θ : ι → ℝ) :
    actualHomotopyAngle η τ ξ (fun i => -θ i) =
      fun i => -actualHomotopyAngle η τ ξ θ i := by
  funext i
  simp only [actualHomotopyAngle_affine_time, actualHomotopyDisplacement_reflection,
    Complex.ofReal_neg]
  ring

theorem actualBalancedJacobian_reflection {ι : Type*} [Fintype ι]
    (η τ ξ : ℝ) (θ : ι → ℝ) :
    actualBalancedJacobian η τ ξ (fun i => -θ i) = actualBalancedJacobian η τ ξ θ := by
  ext v i
  simp only [actualBalancedJacobian, balancedAngularJacobian, LinearMap.coe_mk,
    AddHom.coe_mk, balancedDisplacementDifferential,
    (actual_bump_derivatives_reflection η _).1,
    (actual_bump_derivatives_reflection η _).2,
    lowerPeriodicBump, neg_neg, Complex.ofReal_neg, neg_mul, Finset.sum_neg_distrib]
  ring

theorem isotropicBarePhysicalDensity_reflection {N : ℕ} (s σ : ℂ) (w : Fin N → ℂ) :
    isotropicBarePhysicalDensity s σ (fun i => -w i) = isotropicBarePhysicalDensity s σ w := by
  have hr (i : Fin N) : isotropicInteriorRoot (s, -w i) = isotropicInteriorRoot (s, w i) := by
    simp only [isotropicInteriorRoot, isotropicDispersion, Complex.cos_neg]
  have hp (i j : Fin N) : canceledPair 1
      (isotropicInteriorRoot (s, w i)) (isotropicInteriorRoot (s, w j))
      (Complex.exp (-w i * Complex.I)) (Complex.exp (-w j * Complex.I)) =
        canceledPair 1 (isotropicInteriorRoot (s, w i)) (isotropicInteriorRoot (s, w j))
          (Complex.exp (w i * Complex.I)) (Complex.exp (w j * Complex.I)) := by
    rw [canceledPair_eq_sinePair, canceledPair_eq_sinePair]
    rw [show (-w i - -w j) / 2 = -((w i - w j) / 2) by ring,
      Complex.sin_neg, neg_sq]
  simp only [isotropicBarePhysicalDensity, hr, hp, isotropicDispersion, Complex.cos_neg]

theorem actual_physical_density_reflection {N : ℕ} (η τ ξ : ℝ) (s σ : ℂ) (θ : Fin N → ℝ) :
    homotopyPulledDensity η τ (isotropicBarePhysicalDensity s σ) (ξ, fun i => -θ i) =
      homotopyPulledDensity η τ (isotropicBarePhysicalDensity s σ) (ξ, θ) := by
  rw [homotopyPulledDensity_actual, homotopyPulledDensity_actual,
    actualBalancedJacobian_reflection, actualHomotopyAngle_reflection,
    isotropicBarePhysicalDensity_reflection]

theorem actual_physical_density_reflection_parameter_jets {N : ℕ}
    (η τ ξ : ℝ) (σ : ℂ) (θ : Fin N → ℝ) (j : ℕ) (s : ℂ) :
    iteratedDeriv j (fun z => homotopyPulledDensity η τ
      (isotropicBarePhysicalDensity z σ) (ξ, fun i => -θ i)) s =
      iteratedDeriv j (fun z => homotopyPulledDensity η τ
        (isotropicBarePhysicalDensity z σ) (ξ, θ)) s := by
  congr 2
  funext z
  exact actual_physical_density_reflection η τ ξ z σ θ

end IsingBulk.AnisoF002.Isotropic
