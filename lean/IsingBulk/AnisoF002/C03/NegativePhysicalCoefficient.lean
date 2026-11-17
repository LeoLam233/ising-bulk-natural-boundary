import IsingBulk.AnisoF002.C03.NegativeCoefficientDisks
import IsingBulk.AnisoF002.C03.NegativeGlobalNumerator

/-!
# Exact physical normalization of the full negative-edge coefficient

The original real cycle uses ordinary measure in n independent momenta.
The complete physical numerator already contains [(n+1)!(2pi)^n]^-1.
Its ratio to the matched canonical coefficient is proved simultaneously
for all populations on one fixed disk.  For odd populations this ratio is
the same constant unit phase, so no particle-dependent phase is discarded.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter MeasureTheory IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology BigOperators

def negativePhysicalCoefficient (b B : ℂ → ℂ) (φ : ℝ) (n : ℕ) (t : ℂ) : ℂ :=
  ∫ q in regularAngularBox n,
    completeNegativeNumerator (n + 1) b (negativeGlobalPhase B φ) 0 t
      (fun i => (negativeConstrainedAngles q i : ℂ)) *
        edgeSiteFactor (negativeGlobalCenter B φ) (negativeGlobalCoefficient B)
          t (negativeConstrainedAngles q)

theorem negativePhysicalCoefficient_eq_canonical (b B : ℂ → ℂ) (φ : ℝ) (n : ℕ)
    (ζ t : ℂ) (hb : b t = ζ * edgePrefactor (negativeGlobalCoefficient B) t) :
    negativePhysicalCoefficient b B φ n t =
      ζ ^ ((n + 1) ^ 2) * negativeCanonicalCoefficient B φ n t := by
  unfold negativePhysicalCoefficient
  simp_rw [negative_complete_numerator_eq_global_matched (n + 1) b B φ ζ t
    (negativeConstrainedAngles _) hb]
  simp_rw [mul_assoc]
  rw [integral_const_mul, negativeCanonicalCoefficient_normalization]
  change (ζ ^ ((n + 1) ^ 2) / windingNormalization (n + 1)) *
      (∫ q in regularAngularBox n,
        edgeFullNumerator (negativeGlobalCenter B φ) (negativeGlobalCoefficient B)
          t (negativeConstrainedAngles q) *
        edgeSiteFactor (negativeGlobalCenter B φ) (negativeGlobalCoefficient B)
          t (negativeConstrainedAngles q)) = _
  unfold edgeFullDensity
  ring

theorem unit_imaginary_odd_square_power {ζ : ℂ} (hζ : ζ ^ 2 = -1) {n : ℕ}
    (hn : Odd n) : ζ ^ (n ^ 2) = ζ := by
  obtain ⟨k, rfl⟩ := hn
  have hfour : ζ ^ 4 = 1 := by
    calc
      ζ ^ 4 = (ζ ^ 2) ^ 2 := by ring
      _ = 1 := by rw [hζ]; norm_num
  have he : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
  rw [he, pow_add, pow_mul, hfour, one_pow, one_mul, pow_one]

theorem eventually_physical_odd_coefficients {b B : ℂ → ℂ} (φ : ℝ)
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hBi : (B 0).im < 0) (hbsq : ∀ t, b t ^ 2 = B t) :
    ∃ ζ : ℂ, ζ ^ 2 = -1 ∧ ‖ζ‖ = 1 ∧
      ∀ᶠ t in 𝓝 0, ∀ n : ℕ, Odd (n + 1) →
        negativePhysicalCoefficient b B φ n t = ζ * negativeCanonicalCoefficient B φ n t := by
  obtain ⟨ζ, hζ, hz, he⟩ := physical_root_global_unit_phase hb hB hBi hbsq
  refine ⟨ζ, hζ, hz, he.mono ?_⟩
  intro t ht n hn
  rw [negativePhysicalCoefficient_eq_canonical b B φ n ζ t ht,
    unit_imaginary_odd_square_power hζ hn]

end
end IsingBulk.AnisoF002.NegativeHT
