import IsingBulk.AnisoF002.C03.PhysicalAngularIdentification
import IsingBulk.AnisoF002.C03.RegularEdgeLog

/-!
# Exact even-particle translation at the negative endpoint

The translation of every physical angle by pi preserves the zero-momentum
torus precisely for even particle number.  Its integral preserves the
actual probability measure.  The full anisotropy power is compared as
sqrt(-B)^(N^2) = sqrt(B)^(N^2), without an unstated square-root choice.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open IsingBulk.Anisotropic IsingBulk.AnisoF002.Geometry IsingBulk.First
  MeasureTheory Set
open scoped BigOperators

theorem regularAngularProbability_integral_shift {n : ℕ}
    (f : (Fin n → ℝ) → ℂ) (hf : Continuous f) (hp : CoordinatePeriodic n f)
    (c : Fin n → ℝ) :
    (∫ q, f (fun i => q i + c i) ∂regularAngularProbability n) =
      ∫ q, f q ∂regularAngularProbability n := by
  rw [regularAngularProbability_integral, regularAngularProbability_integral]
  congr 1
  rw [regularAngularBox_integral_eq_shifted, regularAngularBox_integral_eq_shifted]
  have h1 := angleBox_integral_shift n f hf hp (fun i => c i - Real.pi)
  have h2 := angleBox_integral_shift n f hf hp (fun _ => -Real.pi)
  simpa only [sub_eq_add_neg, add_assoc, add_comm (-Real.pi)] using h1.trans h2.symm

theorem flatConstrainedAngles_even_pi_shift {n : ℕ} (hn : Even (n + 1))
    (q : Fin n → ℝ) (i : Fin (n + 1)) :
    realAngleExp (flatConstrainedAngles (fun j => q j + Real.pi) i) =
      realAngleExp (flatConstrainedAngles q i + Real.pi) := by
  obtain ⟨k, hk⟩ := even_iff_exists_two_mul.mp hn
  have hkr : (n : ℝ) + 1 = 2 * (k : ℝ) := by exact_mod_cast hk
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [flatConstrainedAngles, Fin.snoc_last, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have he : -((∑ j, q j) + (n : ℝ) * Real.pi) =
        (-(∑ j, q j) + Real.pi) - (k : ℝ) * (2 * Real.pi) := by
      linear_combination -Real.pi * hkr
    rw [he]
    exact realAngleExp_periodic.sub_nat_mul_eq k
  · simp only [flatConstrainedAngles, Fin.snoc_castSucc]

theorem canonical_even_pi_shift_integral {n : ℕ} {lam : ℝ} {z : ℂ}
    (hn : Even (n + 1)) (hz : z ∉ spectralSetF002 lam) :
    (∫ q, canonicalAngularDensityF002 lam z
      (fun i => flatConstrainedAngles q i + Real.pi) ∂regularAngularProbability n) =
      ∫ q, canonicalAngularDensityF002 lam z (flatConstrainedAngles q)
        ∂regularAngularProbability n := by
  have hpoint (q : Fin n → ℝ) :
      canonicalAngularDensityF002 lam z (fun i => flatConstrainedAngles q i + Real.pi) =
        canonicalAngularDensityF002 lam z (flatConstrainedAngles (fun j => q j + Real.pi)) := by
    exact (canonical_density_congr_angles hz _ _ (flatConstrainedAngles_even_pi_shift hn q)).symm
  simp_rw [hpoint]
  apply regularAngularProbability_integral_shift
    (fun q => canonicalAngularDensityF002 lam z (flatConstrainedAngles q))
    (c := fun _ => Real.pi)
  · exact (canonical_density_continuous_angles (Nat.succ_pos n) hz).comp
      (flatConstrainedAngles_continuous n)
  · exact canonical_constrained_density_periodic hz

theorem square_root_even_square_neg {N : ℕ} (hN : Even N) (B : ℂ) :
    Complex.sqrt (-B) ^ (N ^ 2) = Complex.sqrt B ^ (N ^ 2) := by
  obtain ⟨k, hk⟩ := even_iff_exists_two_mul.mp hN
  have hfour (x : ℂ) : Complex.sqrt x ^ 4 = x ^ 2 := by
    rw [show 4 = 2 * 2 by rfl, pow_mul]
    exact congrArg (fun y : ℂ => y ^ 2) (edgePrefactor_sq (fun _ => x) 0)
  rw [hk, show (2 * k) ^ 2 = 4 * k ^ 2 by ring, pow_mul, pow_mul, hfour, hfour, neg_sq]

theorem edgeFullNumerator_eq_canonical_even_pi {N : ℕ} {lam : ℝ} {z t : ℂ}
    {c a : ℂ → ℂ} (hN : Even N)
    (ha : a t = -(spectralT lam z / spectralS z))
    (hr : ∀ q : ℝ, edgeAngleRoot c a t q = spectralSmallRootF002 lam z (q + Real.pi))
    (x : Fin N → ℝ) :
    edgeFullNumerator c a t x =
      fullRootNumeratorF002 lam z (Complex.sqrt (spectralRatioF002 lam z))
        (fun i => x i + Real.pi) := by
  have hgamma (i : Fin N) : spectralSmallRootF002 lam z (x i + Real.pi) =
      Complex.exp (-edgeAnglePhase c a t (x i)) := by
    rw [← hr, edgeAnglePhase_exp_neg]
  rw [fullRootNumeratorF002_log_branch lam z (Complex.sqrt (spectralRatioF002 lam z)) _ _ hgamma
    (edgePrefactor_sq (spectralRatioF002 lam) z), edgeFullNumerator_log_normalization]
  simp only [add_sub_add_right_eq_sub]
  congr 2
  change Complex.sqrt (a t) ^ (N ^ 2) = _
  rw [ha]
  exact square_root_even_square_neg hN _

theorem edgeFullDensity_eq_canonical_even_pi {N : ℕ} {lam : ℝ} {z t : ℂ}
    {c a : ℂ → ℂ} (hN : Even N)
    (ha : a t = -(spectralT lam z / spectralS z))
    (hr : ∀ q : ℝ, edgeAngleRoot c a t q = spectralSmallRootF002 lam z (q + Real.pi))
    (x : Fin N → ℝ) :
    edgeFullDensity c a t x = canonicalAngularDensityF002 lam z (fun i => x i + Real.pi) := by
  rw [edgeFullDensity, edgeFullNumerator_eq_canonical_even_pi hN ha hr, edgeSiteFactor_eq_product]
  simp only [canonicalAngularDensityF002, hr]

theorem edgeParticleCoefficient_eq_canonical_even_pi {n : ℕ} {lam : ℝ} {z t : ℂ}
    {c a : ℂ → ℂ} (hn : Even (n + 1)) (hz : z ∉ spectralSetF002 lam)
    (ha : a t = -(spectralT lam z / spectralS z))
    (hr : ∀ q : ℝ, edgeAngleRoot c a t q = spectralSmallRootF002 lam z (q + Real.pi)) :
    edgeParticleCoefficient c a n t = canonicalAngularCoefficientF002 lam n z := by
  unfold edgeParticleCoefficient canonicalAngularCoefficientF002
  congr 1
  simp_rw [edgeFullDensity_eq_canonical_even_pi hn ha hr]
  exact canonical_even_pi_shift_integral hn hz

end
end IsingBulk.AnisoF002.RegularTail.C03
