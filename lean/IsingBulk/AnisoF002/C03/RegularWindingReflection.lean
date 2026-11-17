import IsingBulk.AnisoF002.C03.RegularWindingPhysicalSectors

/-!
# Exact reflection of the complete physical winding sectors

Simultaneously negating all real angles preserves the full numerator and
the unique phase pole.  Reflection of the genuine independent-coordinate
measure therefore pairs winding w with winding -w, including the two
first-winding contributions with their original signs.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set MeasureTheory IsingBulk.AnisoF002.RegularTail.C03
open scoped BigOperators

theorem unsignedShortAngle_sq_le_square (x : ℝ) : unsignedShortAngle x ^ 2 ≤ x ^ 2 := by
  by_cases hx : |x| ≤ Real.pi
  · exact (unsignedShortAngle_sq_of_abs_le hx).le
  · have hxp : Real.pi < |x| := lt_of_not_ge hx
    have hu0 := unsignedShortAngle_nonneg x
    have hup := unsignedShortAngle_le_pi x
    have hab := sq_abs x
    nlinarith [Real.pi_pos]

theorem angularShortSquare_le_square {N : ℕ} (q : Fin N → ℝ) :
    angularShortSquare q ≤ ∑ i, q i ^ 2 :=
  Finset.sum_le_sum (fun i _ => unsignedShortAngle_sq_le_square (q i))

theorem angularShortSquare_neg {N : ℕ} (q : Fin N → ℝ) :
    angularShortSquare (-q) = angularShortSquare q := by
  exact angularShortSquare_cos_congr (fun i => Real.cos_neg (q i))

theorem completeNegativeNumerator_neg_real (N : ℕ) (b B : ℂ → ℂ) (φ : ℝ) (t : ℂ)
    (q : Fin N → ℝ) :
    completeNegativeNumerator N b (negativeGlobalPhase B φ) 0 t (fun i => ((-q i : ℝ) : ℂ)) =
      completeNegativeNumerator N b (negativeGlobalPhase B φ) 0 t (fun i => (q i : ℂ)) := by
  unfold completeNegativeNumerator
  simp only [zero_add, Complex.ofReal_neg, negativeGlobalPhase_even]
  simp_rw [show ∀ a b : ℂ, (-a - -b) / 2 = -((a - b) / 2) by intro a b; ring,
    Complex.sin_neg, neg_div, neg_sq]

theorem InnerRemainderFamily.pole_neg_real {b B : ℂ → ℂ}
    {φ r s M kappa R s0 : ℝ} {N : ℕ}
    (d : InnerRemainderFamily b B φ N r s M kappa) (hN : 0 < N)
    (hu : ActualPhaseUniqueOn B φ R s0) (hR : r / (4 * (N : ℝ)) ≤ R) (hs0 : s ≤ s0)
    (q : Fin N → ℝ) (hq : angularShortSquare q ≤ s) : d.pole (-q) = d.pole q := by
  have hq' : angularShortSquare (-q) ≤ s := by rwa [angularShortSquare_neg]
  exact d.pole_cos_equivariant hN hu hR _ q hq' hq (hq'.trans hs0) (fun i => Real.cos_neg (q i))

theorem InnerRemainderFamily.actualResidue_neg_real {b B : ℂ → ℂ}
    {φ r s M kappa R s0 : ℝ} {N : ℕ}
    (d : InnerRemainderFamily b B φ N r s M kappa) (hN : 0 < N)
    (hu : ActualPhaseUniqueOn B φ R s0) (hR : r / (4 * (N : ℝ)) ≤ R) (hs0 : s ≤ s0)
    (q : Fin N → ℝ) (hq : angularShortSquare q ≤ s) : d.actualResidue (-q) = d.actualResidue q := by
  unfold InnerRemainderFamily.actualResidue
  have hphase : realPhaseTotal B φ N (-q) = realPhaseTotal B φ N q :=
    realPhaseTotal_cos_congr B φ (q := -q) (q' := q) (fun i => Real.cos_neg (q i))
  rw [d.pole_neg_real hN hu hR hs0 q hq, hphase]
  congr 2
  exact completeNegativeNumerator_neg_real N b B φ _ q

theorem centeredWindingAngles_neg_winding {n : ℕ} (w : ℤ) (v : Angular.constrainedPlane n) :
    centeredWindingAngles (-w) v = -centeredWindingAngles w (-v) := by
  funext i
  simp only [centeredWindingAngles, windingMean, Int.cast_neg, neg_mul, neg_div, Pi.neg_apply]
  simp only [Submodule.coe_neg, PiLp.neg_apply]
  ring

theorem physicalWindingSectorKernel_neg_winding {b B : ℂ → ℂ}
    {φ r s M kappa R s0 : ℝ} {n : ℕ}
    (d : InnerRemainderFamily b B φ (n + 1) r s M kappa)
    (hu : ActualPhaseUniqueOn B φ R s0) (hR : r / (4 * (n + 1 : ℕ)) ≤ R) (hs0 : s ≤ s0)
    (k : ℕ) (w : ℤ) (v : Angular.constrainedPlane n) :
    physicalWindingSectorKernel d k (-w) v = physicalWindingSectorKernel d k w (-v) := by
  unfold physicalWindingSectorKernel
  simp only [Int.cast_neg, neg_sq, norm_neg]
  by_cases hv : ‖v‖ ^ 2 + (w : ℝ) ^ 2 * Real.pi ^ 2 / (n + 1 : ℕ) ≤ s
  · simp only [hv, ↓reduceIte]
    have hq : angularShortSquare (centeredWindingAngles w (-v)) ≤ s := by
      apply (angularShortSquare_le_square _).trans
      rw [centeredWindingAngles_square, norm_neg]
      exact hv
    rw [centeredWindingAngles_neg_winding,
      d.actualResidue_neg_real (Nat.succ_pos n) hu hR hs0 _ hq,
      d.pole_neg_real (Nat.succ_pos n) hu hR hs0 _ hq]
  · simp only [hv, ↓reduceIte]

theorem physicalWindingSectorCoefficient_neg_winding {b B : ℂ → ℂ}
    {φ r s M kappa R s0 : ℝ} {n : ℕ}
    (d : InnerRemainderFamily b B φ (n + 1) r s M kappa)
    (hu : ActualPhaseUniqueOn B φ R s0) (hR : r / (4 * (n + 1 : ℕ)) ≤ R) (hs0 : s ≤ s0)
    (j : ℕ) (w : ℤ) :
    physicalWindingSectorCoefficient d j (-w) = physicalWindingSectorCoefficient d j w := by
  unfold physicalWindingSectorCoefficient
  simp_rw [physicalWindingSectorKernel_neg_winding d hu hR hs0]
  rw [integral_neg_eq_self]

end
end IsingBulk.AnisoF002.NegativeHT
