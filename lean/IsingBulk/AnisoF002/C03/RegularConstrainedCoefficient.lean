import IsingBulk.AnisoF002.C03.RegularAngularMeasure
import IsingBulk.AnisoF002.C03.RegularEdgeJointDensity
import IsingBulk.AnisoF002.C03.RegularEdgeDensityMajorant
import IsingBulk.AnisoF002.C03.RegularCompactIntegral

/-!
# Complete constrained coefficients and their actual derivatives

There are m+k independent angles and N=m+k+1 particles.  The last angle
is minus their sum, every complete density factor remains present, and
the normalization is exactly 1/[N! (2 pi)^(N-1)].  Differentiation under
the integral is proved from joint analyticity, then the fixed collision
block is integrated while all remaining angle measures have mass one.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

def edgeConstrainedCoefficient (c a : ℂ → ℂ) (m k : ℕ) (t : ℂ) : ℂ :=
  ((m + (k + 1)).factorial : ℂ)⁻¹ *
    ∫ p, edgeFullDensity c a t (splitConstrainedAngles p.1 p.2)
      ∂(regularAngularProbability m).prod (regularAngularProbability k)

def edgeConstrainedCoefficientJet (c a : ℂ → ℂ) (m k j : ℕ) (t : ℂ) : ℂ :=
  ((m + (k + 1)).factorial : ℂ)⁻¹ *
    ∫ p, iteratedDeriv j (fun u => edgeFullDensity c a u (splitConstrainedAngles p.1 p.2)) t
      ∂(regularAngularProbability m).prod (regularAngularProbability k)

theorem edgeConstrainedCoefficient_normalization (c a : ℂ → ℂ) (m k : ℕ) (t : ℂ) :
    edgeConstrainedCoefficient c a m k t =
      (((m + (k + 1)).factorial : ℂ) * (2 * (Real.pi : ℂ)) ^ (m + k))⁻¹ *
        ∫ p in regularAngularBox m ×ˢ regularAngularBox k,
          edgeFullDensity c a t (splitConstrainedAngles p.1 p.2) := by
  rw [edgeConstrainedCoefficient, regularAngularProbability_prod_integral]
  simp only [Complex.real_smul, one_div, Complex.ofReal_inv, Complex.ofReal_pow,
    Complex.ofReal_mul, Complex.ofReal_ofNat, mul_inv_rev]
  ring

theorem complexAngles_continuous (N : ℕ) : Continuous (complexAngles (N := N)) :=
  continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i)

theorem regularAngularProbability_prod_ae_mem (m k : ℕ) :
    ∀ᵐ p ∂(regularAngularProbability m).prod (regularAngularProbability k),
      p ∈ regularAngularBox m ×ˢ regularAngularBox k := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (regularAngularProbability_ae_mem m),
    Measure.quasiMeasurePreserving_snd.ae (regularAngularProbability_ae_mem k)] with p hp hq
  exact ⟨hp, hq⟩

namespace RegularEdgeCompleteControl
variable {b : ℝ} {a : ℂ → ℂ} (d : RegularEdgeCompleteControl b a)

theorem constrained_jet_integrable (m k j : ℕ) {eps : ℝ}
    (he : 0 < eps) (he0 : eps ≤ d.eps0) :
    Integrable (fun p : (Fin m → ℝ) × (Fin k → ℝ) =>
      iteratedDeriv j (fun u => edgeFullDensity (affineEdgeCenter b) a u
        (splitConstrainedAngles p.1 p.2)) ((eps : ℂ) * Complex.I))
      ((regularAngularProbability m).prod (regularAngularProbability k)) := by
  exact integrable_of_carried_compact
    ((regularAngularBox_compact m).prod (regularAngularBox_compact k))
    (regularAngularProbability_prod_ae_mem m k)
    (((d.fullDensity_jet_continuous_inward (by omega : 0 < m + (k + 1)) he he0 j).comp
      (splitConstrainedAngles_continuous m k)).continuousOn)

/-- These are derivatives of the complete coefficient itself, rather than
an independently defined integral of formal density derivatives. -/
theorem constrained_coefficient_iteratedDeriv (m k j : ℕ) {eps : ℝ}
    (he : 0 < eps) (he0 : eps ≤ d.eps0) :
    iteratedDeriv j (edgeConstrainedCoefficient (affineEdgeCenter b) a m k)
        ((eps : ℂ) * Complex.I) =
      edgeConstrainedCoefficientJet (affineEdgeCenter b) a m k j ((eps : ℂ) * Complex.I) := by
  unfold edgeConstrainedCoefficient edgeConstrainedCoefficientJet
  rw [iteratedDeriv_const_mul_field]
  congr 1
  have h := iteratedDeriv_integral_of_joint_analytic
    (μ := (regularAngularProbability m).prod (regularAngularProbability k))
    (f := edgeJointDensity (affineEdgeCenter b) a)
    (g := fun p : (Fin m → ℝ) × (Fin k → ℝ) => complexAngles (splitConstrainedAngles p.1 p.2))
    ((regularAngularBox_compact m).prod (regularAngularBox_compact k))
    (regularAngularProbability_prod_ae_mem m k)
    ((complexAngles_continuous _).comp (splitConstrainedAngles_continuous m k))
    (fun p _ => d.jointDensity_analytic_inward (by omega) he he0 (splitConstrainedAngles p.1 p.2)) j
  simpa only [edgeJointDensity_real] using h

def collisionIntegral (m j : ℕ) : ℝ :=
  ∫ q, retainedCollisionMajorant (m := m) d.kappa (j + 1) q ∂regularAngularProbability m

theorem collisionIntegral_nonneg (m j : ℕ) : 0 ≤ d.collisionIntegral m j :=
  integral_nonneg fun q => retainedCollisionMajorant_nonneg d.kappa_pos.le q

/-- Integrating the fixed block leaves an N-independent finite constant.
The exact factorial prefactor is retained in this coefficient estimate. -/
theorem constrained_coefficient_jet_bound {m k j : ℕ} {eps H : ℝ}
    (hm : 0 < m) (hbudget : 2 * (j + 1) < m ^ 2)
    (he : 0 < eps) (he0 : eps ≤ d.eps0)
    (hbound : ∀ x : Fin (m + (k + 1)) → ℝ,
      (∀ i : Fin m, |x (Fin.castAdd (k + 1) i)| ≤ Real.pi) →
      (fun i : Fin m => x (Fin.castAdd (k + 1) i)) ≠ 0 →
      ‖iteratedDeriv j (fun u => edgeFullDensity (affineEdgeCenter b) a u x)
        ((eps : ℂ) * Complex.I)‖ ≤ H * retainedCollisionMajorant d.kappa (j + 1)
          (fun i : Fin m => x (Fin.castAdd (k + 1) i))) :
    ‖iteratedDeriv j (edgeConstrainedCoefficient (affineEdgeCenter b) a m k)
        ((eps : ℂ) * Complex.I)‖ ≤
      ((m + (k + 1)).factorial : ℝ)⁻¹ * (H * d.collisionIntegral m j) := by
  rw [d.constrained_coefficient_iteratedDeriv m k j he he0,
    edgeConstrainedCoefficientJet, norm_mul, norm_inv, norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  have hi := ((retainedCollisionMajorant_integrable_probability hm hbudget d.kappa_pos).comp_fst
    (regularAngularProbability k)).const_mul H
  have hb : ∀ᵐ p ∂(regularAngularProbability m).prod (regularAngularProbability k),
      ‖iteratedDeriv j (fun u => edgeFullDensity (affineEdgeCenter b) a u
        (splitConstrainedAngles p.1 p.2)) ((eps : ℂ) * Complex.I)‖ ≤
          H * retainedCollisionMajorant d.kappa (j + 1) p.1 := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (regularAngularProbability_ae_mem m),
      Measure.quasiMeasurePreserving_fst.ae (regularAngularProbability_ae_ne_zero hm)] with p hp hp0
    have hpa : ∀ i : Fin m, |p.1 i| ≤ Real.pi := fun i => abs_le.mpr ⟨hp.1 i, hp.2 i⟩
    simpa only [splitConstrainedAngles_first] using
      hbound (splitConstrainedAngles p.1 p.2)
        (by simpa only [splitConstrainedAngles_first] using hpa)
        (by simpa only [splitConstrainedAngles_first] using hp0)
  have hh := norm_integral_le_of_norm_le hi hb
  simpa [integral_const_mul, integral_fun_fst, Measure.real, collisionIntegral] using hh

end RegularEdgeCompleteControl
end
end IsingBulk.AnisoF002.RegularTail.C03
