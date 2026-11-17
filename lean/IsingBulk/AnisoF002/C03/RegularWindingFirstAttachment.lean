import IsingBulk.AnisoF002.C03.RegularWindingReflection
import IsingBulk.AnisoF002.C03.NegativeActualPoleIntegral

/-!
# The two literal first windings and the constructed physical residue

The moving pole, numerator and temperature derivative are compared as
functions.  In particular the minus sign in the Taylor coefficient is
exactly the minus sign already present in physicalResidueIntegrand.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter MeasureTheory Angular IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology BigOperators

def firstWindingCutRadius (n : ℕ) (s : ℝ) : ℝ :=
  Real.sqrt (s - Real.pi ^ 2 / (n + 1 : ℕ))

theorem firstWinding_cut_iff_ball {n : ℕ} {s : ℝ}
    (hs : Real.pi ^ 2 / (n + 1 : ℕ) ≤ s) (v : constrainedPlane n) :
    ‖v‖ ^ 2 + Real.pi ^ 2 / (n + 1 : ℕ) ≤ s ↔
      v ∈ Metric.closedBall 0 (firstWindingCutRadius n s) := by
  rw [Metric.mem_closedBall, dist_zero_right]
  have hr := Real.sq_sqrt (sub_nonneg.mpr hs)
  have hr0 := Real.sqrt_nonneg (s - Real.pi ^ 2 / (n + 1 : ℕ))
  unfold firstWindingCutRadius
  constructor <;> intro h <;> nlinarith [norm_nonneg v]

theorem centeredWindingAngles_one_cast {n : ℕ} (v : constrainedPlane n) (i : Fin (n + 1)) :
    (centeredWindingAngles 1 v i : ℂ) =
      ((Real.pi / ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) + (complexPlaneEmbedding v : Fin (n + 1) → ℂ) i := by
  simp only [centeredWindingAngles, windingMean, Int.cast_one, one_mul, Complex.ofReal_add,
    complexPlaneEmbedding]

theorem completeNegativeNumerator_shift_origin (N : ℕ) (b : ℂ → ℂ)
    (g : ℂ × ℂ → ℂ) (d t : ℂ) (v : Fin N → ℂ) :
    completeNegativeNumerator N b g 0 t (fun i => d + v i) =
      completeNegativeNumerator N b g d t v := by
  simp only [completeNegativeNumerator, zero_add, add_sub_add_left_eq_sub]

theorem realPhaseTotal_deriv_first_center {B : ℂ → ℂ} {φ : ℝ} {n : ℕ}
    (v : constrainedPlane n) (t : ℂ)
    (hg : ∀ i, DifferentiableAt ℂ (negativeGlobalPhase B φ)
      (t, ((Real.pi / ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) +
        (complexPlaneEmbedding v : Fin (n + 1) → ℂ) i)) :
    deriv (realPhaseTotal B φ (n + 1) (centeredWindingAngles 1 v)) t =
      phaseTemperatureSum (n + 1) (negativeGlobalPhase B φ)
        ((Real.pi / ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) t (complexPlaneEmbedding v) := by
  have he : realPhaseTotal B φ (n + 1) (centeredWindingAngles 1 v) = fun u =>
      ∑ i, negativeGlobalPhase B φ (u, ((Real.pi / ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) +
        (complexPlaneEmbedding v : Fin (n + 1) → ℂ) i) := by
    funext u
    simp only [realPhaseTotal, centeredWindingAngles_one_cast]
  rw [he]
  exact (phaseTemperatureSum_hasDerivAt (n + 1) (negativeGlobalPhase B φ) _ t _ hg).deriv

theorem physicalWindingSectorKernel_first {b B : ℂ → ℂ}
    {φ r s M kappa R s0 σ C Kρ Kp : ℝ} {n : ℕ}
    (d : InnerRemainderFamily b B φ (n + 1) r s M kappa)
    (p : PhysicalFirstWindingData b B φ (n + 1) σ C Kρ Kp)
    (hu : ActualPhaseUniqueOn B φ R s0) (hR : r / (4 * (n + 1 : ℕ)) ≤ R)
    (hs0 : s ≤ s0) (hsσ : s < σ ^ 2) (k : ℕ)
    (v : constrainedPlane n) (hv : ‖v‖ ^ 2 + Real.pi ^ 2 / (n + 1 : ℕ) ≤ s)
    (hp : ‖p.pole (complexPlaneEmbedding v)‖ ≤ R)
    (hg : ∀ i, DifferentiableAt ℂ (negativeGlobalPhase B φ)
      (p.pole (complexPlaneEmbedding v),
        ((Real.pi / ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) + (complexPlaneEmbedding v : Fin (n + 1) → ℂ) i)) :
    physicalWindingSectorKernel d k 1 v = -p.physicalResidueIntegrand k v := by
  have hQ : displacementSquare (n + 1) (complexPlaneEmbedding v) < σ ^ 2 := by
    rw [complexPlaneEmbedding_square]
    have hc : 0 ≤ Real.pi ^ 2 / ((n + 1 : ℕ) : ℝ) := by positivity
    linarith
  have hq : angularShortSquare (centeredWindingAngles 1 v) ≤ s := by
    apply (angularShortSquare_le_square _).trans
    simpa only [centeredWindingAngles_square, Int.cast_one, one_pow, one_mul] using hv
  have hpole := d.pole_eq_first_winding p (Nat.succ_pos n) hu hR _ hq (hq.trans hs0)
    (complexPlaneEmbedding v) hQ hp (fun i => congrArg Complex.cos (centeredWindingAngles_one_cast v i))
  unfold physicalWindingSectorKernel
  simp only [Int.cast_one, one_pow, one_mul, hv, ↓reduceIte]
  unfold InnerRemainderFamily.actualResidue
  rw [hpole, realPhaseTotal_deriv_first_center v _ hg]
  have hnum : completeNegativeNumerator (n + 1) b (negativeGlobalPhase B φ) 0
      (p.pole (complexPlaneEmbedding v)) (fun i => (centeredWindingAngles 1 v i : ℂ)) =
    completeNegativeNumerator (n + 1) b (negativeGlobalPhase B φ)
      ((Real.pi / ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) (p.pole (complexPlaneEmbedding v))
      (complexPlaneEmbedding v) := by
    simp_rw [centeredWindingAngles_one_cast]
    exact completeNegativeNumerator_shift_origin _ _ _ _ _ _
  rw [hnum]
  unfold PhysicalFirstWindingData.physicalResidueIntegrand
  ring

theorem physicalWindingSectorCoefficient_first {b B : ℂ → ℂ}
    {φ r s M kappa R s0 σ C Kρ Kp : ℝ} {n : ℕ}
    (d : InnerRemainderFamily b B φ (n + 1) r s M kappa)
    (p : PhysicalFirstWindingData b B φ (n + 1) σ C Kρ Kp)
    (hu : ActualPhaseUniqueOn B φ R s0) (hR : r / (4 * (n + 1 : ℕ)) ≤ R)
    (hs0 : s ≤ s0) (hsσ : s < σ ^ 2) (hsN : Real.pi ^ 2 / (n + 1 : ℕ) ≤ s)
    (hp : ∀ v : constrainedPlane n, ‖v‖ ^ 2 + Real.pi ^ 2 / (n + 1 : ℕ) ≤ s →
      ‖p.pole (complexPlaneEmbedding v)‖ ≤ R)
    (hg : ∀ v : constrainedPlane n, ‖v‖ ^ 2 + Real.pi ^ 2 / (n + 1 : ℕ) ≤ s →
      ∀ i, DifferentiableAt ℂ (negativeGlobalPhase B φ)
        (p.pole (complexPlaneEmbedding v),
          ((Real.pi / ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) + (complexPlaneEmbedding v : Fin (n + 1) → ℂ) i))
    (j : ℕ) :
    physicalWindingSectorCoefficient d j 1 = p.physicalResidueIntegral (j + 1) (firstWindingCutRadius n s) := by
  unfold physicalWindingSectorCoefficient PhysicalFirstWindingData.physicalResidueIntegral
  rw [← integral_neg, ← integral_indicator measurableSet_closedBall]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro v
  dsimp only
  by_cases hv : ‖v‖ ^ 2 + Real.pi ^ 2 / (n + 1 : ℕ) ≤ s
  · rw [indicator_of_mem ((firstWinding_cut_iff_ball hsN v).mp hv),
      physicalWindingSectorKernel_first d p hu hR hs0 hsσ _ v hv (hp v hv) (hg v hv), neg_neg]
  · rw [indicator_of_notMem (fun h => hv ((firstWinding_cut_iff_ball hsN v).mpr h))]
    simp only [physicalWindingSectorKernel, Int.cast_one, one_pow, one_mul, hv, ↓reduceIte, neg_zero]

theorem physical_first_winding_pair_eq {b B : ℂ → ℂ}
    {φ r s M kappa R s0 : ℝ} {n : ℕ}
    (d : InnerRemainderFamily b B φ (n + 1) r s M kappa)
    (hu : ActualPhaseUniqueOn B φ R s0) (hR : r / (4 * (n + 1 : ℕ)) ≤ R) (hs0 : s ≤ s0)
    (j : ℕ) :
    physicalWindingSectorCoefficient d j 1 + physicalWindingSectorCoefficient d j (-1) =
      2 * physicalWindingSectorCoefficient d j 1 := by
  rw [physicalWindingSectorCoefficient_neg_winding d hu hR hs0 j 1]
  ring

end
end IsingBulk.AnisoF002.NegativeHT
