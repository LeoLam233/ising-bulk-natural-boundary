import IsingBulk.AnisoF002.C03.RegularCollisionIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Actual independent angular coordinates and their normalized measures

Each finite block uses normalized Lebesgue measure on [-pi,pi]^m.  Its
mass is exactly one, including the empty block.  The last angle is minus
the sum of all independent angles.  No surface-measure Jacobian replaces
the independent-coordinate normalization.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set MeasureTheory
open scoped BigOperators Topology

def regularAngularProbability (m : ℕ) : Measure (Fin m → ℝ) :=
  (ENNReal.ofReal ((2 * Real.pi) ^ m))⁻¹ • volume.restrict (regularAngularBox m)

theorem regularAngularBox_volume (m : ℕ) :
    volume (regularAngularBox m) = ENNReal.ofReal ((2 * Real.pi) ^ m) := by
  rw [regularAngularBox, Real.volume_Icc_pi]
  simp only [sub_neg_eq_add, ← two_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow (by positivity)]

instance regularAngularProbability_isProbability (m : ℕ) : IsProbabilityMeasure (regularAngularProbability m) where
  measure_univ := by
    rw [regularAngularProbability, Measure.smul_apply, Measure.restrict_apply_univ,
      regularAngularBox_volume, smul_eq_mul, ENNReal.inv_mul_cancel]
    · exact ENNReal.ofReal_ne_zero_iff.mpr (pow_pos (by positivity : (0 : ℝ) < 2 * Real.pi) m)
    · exact ENNReal.ofReal_ne_top

theorem regularAngularProbability_ae_mem (m : ℕ) :
    ∀ᵐ x ∂regularAngularProbability m, x ∈ regularAngularBox m :=
  Measure.ae_smul_measure (self_mem_ae_restrict (regularAngularBox_compact m).isClosed.measurableSet) _

theorem regularAngularProbability_ae_ne_zero {m : ℕ} (hm : 0 < m) :
    ∀ᵐ x ∂regularAngularProbability m, x ≠ 0 := by
  let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  exact Measure.ae_smul_measure (ae_restrict_of_ae (volume.ae_ne (0 : Fin m → ℝ))) _

theorem retainedCollisionMajorant_integrable_probability {m p : ℕ} {kappa : ℝ}
    (hm : 0 < m) (hbudget : 2 * p < m ^ 2) (hk : 0 < kappa) :
    Integrable (retainedCollisionMajorant (m := m) kappa p) (regularAngularProbability m) := by
  apply (retainedCollisionMajorant_integrable hm hbudget hk).smul_measure
  exact ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr
    (pow_pos (by positivity : (0 : ℝ) < 2 * Real.pi) m))

theorem regularAngularProbability_integral {m : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : (Fin m → ℝ) → F) :
    ∫ x, f x ∂regularAngularProbability m =
      (1 / (2 * Real.pi) ^ m : ℝ) • ∫ x in regularAngularBox m, f x := by
  rw [regularAngularProbability, integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (pow_nonneg (by positivity) m), one_div]

theorem regularAngularProbability_prod_integral {m k : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : (Fin m → ℝ) × (Fin k → ℝ) → F) :
    ∫ x, f x ∂(regularAngularProbability m).prod (regularAngularProbability k) =
      (1 / (2 * Real.pi) ^ (m + k) : ℝ) •
        ∫ x in regularAngularBox m ×ˢ regularAngularBox k, f x := by
  rw [regularAngularProbability, regularAngularProbability, Measure.prod_smul_left,
    Measure.prod_smul_right, smul_smul, integral_smul_measure]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (pow_nonneg (show (0 : ℝ) ≤ 2 * Real.pi by positivity) m),
    ENNReal.toReal_ofReal (pow_nonneg (show (0 : ℝ) ≤ 2 * Real.pi by positivity) k)]
  rw [Measure.prod_restrict, pow_add, one_div, mul_inv_rev, mul_comm]
  rfl

def splitConstrainedAngles {m k : ℕ} (q : Fin m → ℝ) (y : Fin k → ℝ) :
    Fin (m + (k + 1)) → ℝ := Fin.append q (Fin.snoc y (-(∑ i, q i) - ∑ i, y i))

theorem splitConstrainedAngles_first {m k : ℕ} (q : Fin m → ℝ) (y : Fin k → ℝ) (i : Fin m) :
    splitConstrainedAngles q y (Fin.castAdd (k + 1) i) = q i := by simp [splitConstrainedAngles]

theorem splitConstrainedAngles_sum {m k : ℕ} (q : Fin m → ℝ) (y : Fin k → ℝ) :
    ∑ i, splitConstrainedAngles q y i = 0 := by
  simp [splitConstrainedAngles, Fin.sum_univ_add, Fin.sum_univ_castSucc]

theorem splitConstrainedAngles_continuous (m k : ℕ) :
    Continuous (fun p : (Fin m → ℝ) × (Fin k → ℝ) => splitConstrainedAngles p.1 p.2) := by
  unfold splitConstrainedAngles
  apply (Fin.continuous_append m (k + 1)).comp
    (f := fun p : (Fin m → ℝ) × (Fin k → ℝ) =>
      (p.1, Fin.snoc p.2 (-(∑ i, p.1 i) - ∑ i, p.2 i)))
  have hlast : Continuous (fun p : (Fin m → ℝ) × (Fin k → ℝ) =>
      -(∑ i, p.1 i) - ∑ i, p.2 i) :=
    (continuous_finsetSum _ fun i _ => (continuous_apply i).comp continuous_fst).neg.sub
      (continuous_finsetSum _ fun i _ => (continuous_apply i).comp continuous_snd)
  exact continuous_fst.prodMk (continuous_snd.finSnoc (A := fun _ : Fin (k + 1) => ℝ) hlast)

end
end IsingBulk.AnisoF002.RegularTail.C03
