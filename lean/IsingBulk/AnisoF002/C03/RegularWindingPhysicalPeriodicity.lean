import IsingBulk.AnisoF002.C03.RegularWindingSectorPartition
import IsingBulk.AnisoF002.C03.NegativeCyclePoleUniqueness
import IsingBulk.AnisoF002.C03.NegativeCyclePoleRepresentation

/-!
# Integer-period invariance of the actual complete pole density

The pole is the same unique actual phase zero after changing signed lifts.
The squared half-angle numerators, all one-body factors, the physical
square-root power, and the exact temperature derivative are retained.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set MeasureTheory IsingBulk.AnisoF002.RegularTail.C03
open scoped BigOperators

theorem angularShortSquare_cos_congr {N : ℕ} {q q' : Fin N → ℝ}
    (hcos : ∀ i, Real.cos (q i) = Real.cos (q' i)) :
    angularShortSquare q = angularShortSquare q' := by
  unfold angularShortSquare unsignedShortAngle
  simp_rw [hcos]

theorem angularShortSquare_integer_period {N : ℕ} (k : Fin N → ℤ) (q : Fin N → ℝ) :
    angularShortSquare (fun i => q i + (k i : ℝ) * (2 * Real.pi)) = angularShortSquare q :=
  angularShortSquare_cos_congr (fun i => Real.cos_add_int_mul_two_pi (q i) (k i))

theorem complex_half_sine_square_integer_period (x y : ℝ) (k l : ℤ) :
    Complex.sin ((((x + (k : ℝ) * (2 * Real.pi) : ℝ) : ℂ) -
      ((y + (l : ℝ) * (2 * Real.pi) : ℝ) : ℂ)) / 2) ^ 2 =
      Complex.sin (((x : ℂ) - (y : ℂ)) / 2) ^ 2 := by
  have hr : Real.sin ((x + (k : ℝ) * (2 * Real.pi) -
      (y + (l : ℝ) * (2 * Real.pi))) / 2) ^ 2 = Real.sin ((x - y) / 2) ^ 2 := by
    simp only [Real.sin_sq_eq_half_sub]
    have he : 2 * ((x + (k : ℝ) * (2 * Real.pi) -
        (y + (l : ℝ) * (2 * Real.pi))) / 2) =
        (x - y) + ((k - l : ℤ) : ℝ) * (2 * Real.pi) := by push_cast; ring
    rw [he, Real.cos_add_int_mul_two_pi]
    congr 2
    ring
  exact_mod_cast hr

theorem completeNegativeNumerator_integer_period (N : ℕ) (b B : ℂ → ℂ) (φ : ℝ) (t : ℂ)
    (k : Fin N → ℤ) (q : Fin N → ℝ) :
    completeNegativeNumerator N b (negativeGlobalPhase B φ) 0 t
      (fun i => ((q i + (k i : ℝ) * (2 * Real.pi) : ℝ) : ℂ)) =
    completeNegativeNumerator N b (negativeGlobalPhase B φ) 0 t (fun i => (q i : ℂ)) := by
  have hg (i : Fin N) :
      negativeGlobalPhase B φ (t, ((q i + (k i : ℝ) * (2 * Real.pi) : ℝ) : ℂ)) =
      negativeGlobalPhase B φ (t, (q i : ℂ)) := by
    apply negativeGlobalPhase_cos_congr
    simp only [← Complex.ofReal_cos, Real.cos_add_int_mul_two_pi]
  unfold completeNegativeNumerator
  simp only [zero_add]
  simp_rw [hg]
  congr 1
  apply Finset.prod_congr rfl
  intro ij _
  rw [div_pow, div_pow, complex_half_sine_square_integer_period]

def actualInnerPoleDensity {b B : ℂ → ℂ} {φ r s M kappa : ℝ} {N : ℕ}
    (d : InnerRemainderFamily b B φ N r s M kappa) (j : ℕ) : (Fin N → ℝ) → ℂ :=
  shortCutDensity s (fun q => d.actualResidue q / d.pole q ^ (j + 1))

theorem InnerRemainderFamily.actualResidue_integer_period {b B : ℂ → ℂ}
    {φ r s M kappa R s0 : ℝ} {N : ℕ}
    (d : InnerRemainderFamily b B φ N r s M kappa) (hN : 0 < N)
    (hu : ActualPhaseUniqueOn B φ R s0) (hR : r / (4 * (N : ℝ)) ≤ R) (hs0 : s ≤ s0)
    (k : Fin N → ℤ) (q : Fin N → ℝ) (hq : angularShortSquare q ≤ s) :
    d.actualResidue (fun i => q i + (k i : ℝ) * (2 * Real.pi)) = d.actualResidue q := by
  have hc (i : Fin N) : Real.cos (q i + (k i : ℝ) * (2 * Real.pi)) = Real.cos (q i) :=
    Real.cos_add_int_mul_two_pi _ _
  have hq' : angularShortSquare (fun i => q i + (k i : ℝ) * (2 * Real.pi)) ≤ s := by
    rwa [angularShortSquare_integer_period]
  have hp := d.pole_cos_equivariant hN hu hR _ q hq' hq (hq'.trans hs0) hc
  unfold InnerRemainderFamily.actualResidue
  rw [hp, realPhaseTotal_cos_congr B φ hc, completeNegativeNumerator_integer_period]

theorem actualInnerPoleDensity_periodic {b B : ℂ → ℂ}
    {φ r s M kappa R s0 : ℝ} {N : ℕ}
    (d : InnerRemainderFamily b B φ N r s M kappa) (hN : 0 < N)
    (hu : ActualPhaseUniqueOn B φ R s0) (hR : r / (4 * (N : ℝ)) ≤ R) (hs0 : s ≤ s0) (j : ℕ) :
    AllAnglePeriodic (actualInnerPoleDensity d j) := by
  intro k q
  unfold actualInnerPoleDensity shortCutDensity
  rw [angularShortSquare_integer_period]
  by_cases hq : angularShortSquare q ≤ s
  · simp only [hq, ↓reduceIte]
    have hq' : angularShortSquare (fun i => q i + (k i : ℝ) * (2 * Real.pi)) ≤ s := by
      rwa [angularShortSquare_integer_period]
    rw [d.actualResidue_integer_period hN hu hR hs0 k q hq,
      d.pole_cos_equivariant hN hu hR _ q hq' hq (hq'.trans hs0)
        (fun i => Real.cos_add_int_mul_two_pi _ _)]
  · simp only [hq, ↓reduceIte]

theorem innerCyclePoleCoefficient_eq_density {b B : ℂ → ℂ}
    {φ r s M kappa : ℝ} {n : ℕ}
    (d : InnerRemainderFamily b B φ (n + 1) r s M kappa) (j : ℕ) :
    innerCyclePoleCoefficient d j =
      -(∫ q in regularAngularBox n, actualInnerPoleDensity d j (negativeConstrainedAngles q)) := rfl

end
end IsingBulk.AnisoF002.NegativeHT
