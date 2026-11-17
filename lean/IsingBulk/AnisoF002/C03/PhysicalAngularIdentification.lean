import IsingBulk.AnisoF002.C03.PhysicalAngularRegularity
import IsingBulk.First.PeriodicBoxIntegral

/-!
# Exact identification with the original real constrained coefficients

The independent-coordinate measure is translated from [-pi,pi]^n to the
original [0,2pi]^n convention and then matched to the actual recursive
integral.  Its normalization and dependent last angle are unchanged.
Only separately audited generic finite Fubini and periodic-shift support
is used from the historical tree.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set MeasureTheory IsingBulk.Anisotropic IsingBulk.Anisotropic.FormFactors
  IsingBulk.AnisoF002.Geometry IsingBulk.First
open scoped BigOperators

theorem regularAngularBox_integral_eq_shifted (n : ℕ) (f : (Fin n → ℝ) → ℂ) :
    (∫ x in regularAngularBox n, f x) =
      ∫ x in angleBox n, f (fun i => x i - Real.pi) := by
  let c : Fin n → ℝ := fun _ => Real.pi
  have hpre : (fun x : Fin n → ℝ => x + c) ⁻¹' angleBox n = regularAngularBox n := by
    ext x
    simp only [mem_preimage, angleBox, regularAngularBox, mem_Icc, Pi.le_def, Pi.add_apply, c]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun i => by linarith [h1 i], fun i => by linarith [h2 i]⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun i => by linarith [h1 i], fun i => by linarith [h2 i]⟩
  have hh := (measurePreserving_add_right (volume : Measure (Fin n → ℝ)) c).setIntegral_preimage_emb
    (MeasurableEquiv.addRight c).measurableEmbedding
    (fun x : Fin n → ℝ => f (fun i => x i - Real.pi)) (angleBox n)
  rw [hpre] at hh
  simpa only [Pi.add_apply, c, add_sub_cancel_right] using hh

theorem regularAngularBox_integral_eq_original {n : ℕ} (f : (Fin n → ℝ) → ℂ)
    (hf : Continuous f) (hp : CoordinatePeriodic n f) :
    (∫ q in regularAngularBox n, f q) = multiAngleIntegral n f := by
  rw [regularAngularBox_integral_eq_shifted, multiAngleIntegral_eq_box n f hf]
  simpa only [sub_eq_add_neg] using angleBox_integral_shift n f hf hp (fun _ => -Real.pi)

theorem regularAngularProbability_eq_original {n : ℕ} (f : (Fin n → ℝ) → ℂ)
    (hf : Continuous f) (hp : CoordinatePeriodic n f) :
    (∫ q, f q ∂regularAngularProbability n) =
      ((2 * (Real.pi : ℂ))⁻¹) ^ n * multiAngleIntegral n f := by
  rw [regularAngularProbability_integral, regularAngularBox_integral_eq_original f hf hp]
  simp only [Complex.real_smul, one_div, Complex.ofReal_inv,
    Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_ofNat, inv_pow]

theorem canonical_coefficient_eq_published_real (n : ℕ) {lam x : ℝ}
    (hlam : 0 < lam) (hx : 0 < x) (hp : realProduct lam x ≠ 1) :
    canonicalAngularCoefficientF002 lam n (x : ℂ) =
      angularCoefficient n (realB lam x) (realC lam x) := by
  have hz := positive_real_not_mem_spectralSetF002 hlam hx hp
  have hflat : Continuous (flatConstrainedAngles (n := n)) := by
    unfold flatConstrainedAngles
    have hlast : Continuous (fun q : Fin n → ℝ => -(∑ i, q i)) :=
      (continuous_finsetSum Finset.univ fun i _ => continuous_apply i).neg
    exact continuous_id.finSnoc (A := fun _ : Fin (n + 1) => ℝ) hlast
  have hc : Continuous (fun q : Fin n → ℝ =>
      canonicalAngularDensityF002 lam (x : ℂ) (flatConstrainedAngles q)) :=
    (canonical_density_continuous_angles (Nat.succ_pos n) hz).comp hflat
  have hperiod : CoordinatePeriodic n
      (fun q => canonicalAngularDensityF002 lam (x : ℂ) (flatConstrainedAngles q)) :=
    canonical_constrained_density_periodic hz
  rw [canonicalAngularCoefficientF002, regularAngularProbability_eq_original _ hc hperiod]
  simp only [canonical_density_eq_published_real hlam hx hp,
    angularCoefficient, IsingBulk.HT.Contour.physicalDependentAngles, flatConstrainedAngles]
  ring

end
end IsingBulk.AnisoF002.RegularTail.C03
