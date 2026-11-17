import IsingBulk.AnisoF002.C03.PhysicalCanonicalRoot
import IsingBulk.AnisoF002.C03.PhysicalVerticalDensity
import IsingBulk.AnisoF002.C03.PhysicalGlobalHolomorphy

/-!
# The actual normalized canonical angular density on the full complement

Each one-body factor is divided by S using the filled canonical quotient.
Every canceled pair is retained, with its coefficient ST and its original
root denominator.  The resulting complete density is jointly analytic
even at S=0.  Its actual constrained integral is analytic on the full
unsquared spectral complement.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set Filter MeasureTheory IsingBulk.Anisotropic IsingBulk.Anisotropic.FormFactors
  IsingBulk.AnisoF002.Geometry IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators

def physicalCanonicalOneBody (lam : ℝ) (p : ℂ × ℂ) : ℂ :=
  2 * physicalRootQuotient lam p / (1 - physicalComplexRoot lam p ^ 2)

def physicalCanonicalPair (lam : ℝ) (p : ℂ × (ℂ × ℂ)) : ℂ :=
  -spectralProduct lam p.1 * (Complex.exp (p.2.1 * Complex.I) - Complex.exp (p.2.2 * Complex.I)) ^ 2 *
    physicalRootQuotient lam (p.1, p.2.1) * physicalRootQuotient lam (p.1, p.2.2) /
    (Complex.exp (p.2.1 * Complex.I) * Complex.exp (p.2.2 * Complex.I) *
      (1 - physicalComplexRoot lam (p.1, p.2.1) * physicalComplexRoot lam (p.1, p.2.2)) ^ 2)

def physicalCanonicalNumerator {N : ℕ} (lam : ℝ) (p : ℂ × (Fin N → ℂ)) : ℂ :=
  (∏ i, physicalCanonicalOneBody lam (p.1, p.2 i)) *
    ∏ ij ∈ indexPairs N, physicalCanonicalPair lam (p.1, p.2 ij.1, p.2 ij.2)

def physicalCanonicalDensity {N : ℕ} (lam : ℝ) (p : ℂ × (Fin N → ℂ)) : ℂ :=
  physicalCanonicalNumerator lam p *
    ((1 + ∏ i, physicalComplexRoot lam (p.1, p.2 i)) /
      (1 - ∏ i, physicalComplexRoot lam (p.1, p.2 i)))

def physicalCanonicalCoefficient (lam : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  ((n + 1).factorial : ℂ)⁻¹ *
    ∫ q, physicalCanonicalDensity lam (z, complexAngles (flatConstrainedAngles q))
      ∂regularAngularProbability n

theorem physicalCanonicalOneBody_analyticAt {lam : ℝ} {z : ℂ} (q : ℝ)
    (hz : z ∉ spectralSetF002 lam) : AnalyticAt ℂ (physicalCanonicalOneBody lam) (z, (q : ℂ)) := by
  apply (analyticAt_const.mul (physicalRootQuotient_analyticAt q hz)).div
    (analyticAt_const.sub ((physicalComplexRoot_analyticAt q hz).pow 2))
  change 1 - physicalComplexRoot lam (z, (q : ℂ)) ^ 2 ≠ 0
  rw [physicalComplexRoot_real q hz]
  simpa only [pow_two] using pair_root_denominator_ne_zero
    (spectralSmallRootF002_spec q hz).2 (spectralSmallRootF002_spec q hz).2

theorem physicalCanonicalPair_analyticAt {lam : ℝ} {z : ℂ} (q t : ℝ)
    (hz : z ∉ spectralSetF002 lam) :
    AnalyticAt ℂ (physicalCanonicalPair lam) (z, (q : ℂ), (t : ℂ)) := by
  let p : ℂ × (ℂ × ℂ) := (z, (q : ℂ), (t : ℂ))
  have hq : AnalyticAt ℂ (fun a : ℂ × (ℂ × ℂ) => (a.1, a.2.1)) p :=
    analyticAt_fst.prod (analyticAt_fst.comp analyticAt_snd)
  have ht : AnalyticAt ℂ (fun a : ℂ × (ℂ × ℂ) => (a.1, a.2.2)) p :=
    analyticAt_fst.prod (analyticAt_snd.comp analyticAt_snd)
  have hRq := (physicalComplexRoot_analyticAt q hz).comp_of_eq hq rfl
  have hRt := (physicalComplexRoot_analyticAt t hz).comp_of_eq ht rfl
  have hQq := (physicalRootQuotient_analyticAt q hz).comp_of_eq hq rfl
  have hQt := (physicalRootQuotient_analyticAt t hz).comp_of_eq ht rfl
  have hYq : AnalyticAt ℂ (fun a : ℂ × (ℂ × ℂ) => Complex.exp (a.2.1 * Complex.I)) p :=
    (analyticAt_fst.comp analyticAt_snd).mul analyticAt_const |>.cexp
  have hYt : AnalyticAt ℂ (fun a : ℂ × (ℂ × ℂ) => Complex.exp (a.2.2 * Complex.I)) p :=
    (analyticAt_snd.comp analyticAt_snd).mul analyticAt_const |>.cexp
  apply (((((Physical.spectralProduct_analytic lam z).comp analyticAt_fst).neg.mul
    ((hYq.sub hYt).pow 2)).mul hQq).mul hQt).div
      ((hYq.mul hYt).mul ((analyticAt_const.sub (hRq.mul hRt)).pow 2))
  change Complex.exp ((q : ℂ) * Complex.I) * Complex.exp ((t : ℂ) * Complex.I) *
    (1 - physicalComplexRoot lam (z, (q : ℂ)) * physicalComplexRoot lam (z, (t : ℂ))) ^ 2 ≠ 0
  rw [physicalComplexRoot_real q hz, physicalComplexRoot_real t hz]
  exact mul_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _))
    (pow_ne_zero _ (pair_root_denominator_ne_zero
      (spectralSmallRootF002_spec q hz).2 (spectralSmallRootF002_spec t hz).2))

theorem physicalCanonicalNumerator_analyticAt {N : ℕ} {lam : ℝ} {z : ℂ}
    (q : Fin N → ℝ) (hz : z ∉ spectralSetF002 lam) :
    AnalyticAt ℂ (physicalCanonicalNumerator lam) (z, complexAngles q) := by
  have hcoord (i : Fin N) : AnalyticAt ℂ (fun p : ℂ × (Fin N → ℂ) => (p.1, p.2 i))
      (z, complexAngles q) := analyticAt_fst.prod (analyticAt_angle_coordinate i _)
  apply (Finset.univ.analyticAt_fun_prod fun i _ =>
    (physicalCanonicalOneBody_analyticAt (q i) hz).comp_of_eq (hcoord i) rfl).mul
      ((indexPairs N).analyticAt_fun_prod fun ij _ => ?_)
  exact (physicalCanonicalPair_analyticAt (q ij.1) (q ij.2) hz).comp_of_eq
    (analyticAt_fst.prod ((analyticAt_angle_coordinate ij.1 _).prod (analyticAt_angle_coordinate ij.2 _))) rfl

theorem physicalCanonicalDensity_analyticAt {N : ℕ} (hN : 0 < N) {lam : ℝ} {z : ℂ}
    (q : Fin N → ℝ) (hz : z ∉ spectralSetF002 lam) :
    AnalyticAt ℂ (physicalCanonicalDensity lam) (z, complexAngles q) := by
  have hprod : AnalyticAt ℂ (fun p : ℂ × (Fin N → ℂ) =>
      ∏ i, physicalComplexRoot lam (p.1, p.2 i)) (z, complexAngles q) :=
    Finset.univ.analyticAt_fun_prod fun i _ =>
      (physicalComplexRoot_analyticAt (q i) hz).comp_of_eq
        (analyticAt_fst.prod (analyticAt_angle_coordinate i _)) rfl
  apply (physicalCanonicalNumerator_analyticAt q hz).mul
    ((analyticAt_const.add hprod).div (analyticAt_const.sub hprod) ?_)
  change 1 - (∏ i, physicalComplexRoot lam (z, complexAngles q i)) ≠ 0
  simp only [complexAngles, physicalComplexRoot_real _ hz]
  exact canonical_root_product_denominator hN hz q

theorem physicalCanonicalCoefficient_analyticAt (n : ℕ) {lam : ℝ} {z : ℂ}
    (hz : z ∉ spectralSetF002 lam) : AnalyticAt ℂ (physicalCanonicalCoefficient lam n) z := by
  have hc : Continuous (fun q : Fin n → ℝ => complexAngles (flatConstrainedAngles q)) :=
    (continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i)).comp
      (literal_flatAngles_continuous n)
  exact analyticAt_const.mul (analyticAt_integral_of_joint_analytic
    (regularAngularBox_compact n) (regularAngularProbability_ae_mem n) hc
    (fun q _ => physicalCanonicalDensity_analyticAt (Nat.succ_pos n) (flatConstrainedAngles q) hz))

theorem physicalCanonicalCoefficient_analyticOnNhd (lam : ℝ) (n : ℕ) :
    AnalyticOnNhd ℂ (physicalCanonicalCoefficient lam n) (spectralSetF002 lam)ᶜ :=
  fun _ hz => physicalCanonicalCoefficient_analyticAt n hz

theorem spectralOneBody_eq_physicalCanonical {lam : ℝ} {z : ℂ} (q : ℝ)
    (hz : z ∉ spectralSetF002 lam) :
    spectralOneBodyF002 lam z q = spectralS z * physicalCanonicalOneBody lam (z, (q : ℂ)) := by
  unfold spectralOneBodyF002 physicalCanonicalOneBody
  rw [physicalComplexRoot_real q hz, ← physicalRootQuotient_mul_spectralS q hz]
  ring

theorem spectralCanceledPair_eq_physicalCanonical {lam : ℝ} {z : ℂ} (q t : ℝ)
    (hz : z ∉ spectralSetF002 lam) :
    spectralCanceledPairF002 lam z q t = physicalCanonicalPair lam (z, (q : ℂ), (t : ℂ)) := by
  unfold spectralCanceledPairF002 canceledPair physicalCanonicalPair
  rw [physicalComplexRoot_real q hz, physicalComplexRoot_real t hz]
  congr 1
  by_cases hS : spectralS z = 0
  · simp only [hS, div_zero, neg_zero, zero_mul, spectralProduct]
  · rw [← physicalRootQuotient_mul_spectralS q hz, ← physicalRootQuotient_mul_spectralS t hz]
    unfold spectralProduct
    field_simp

theorem fullRootNumerator_eq_physicalCanonical {N : ℕ} {lam : ℝ} {z b : ℂ}
    (q : Fin N → ℝ) (hz : z ∉ spectralSetF002 lam) :
    fullRootNumeratorF002 lam z b q = (spectralS z * b) ^ N *
      physicalCanonicalNumerator lam (z, complexAngles q) := by
  unfold fullRootNumeratorF002 physicalCanonicalNumerator
  simp only [spectralOneBody_eq_physicalCanonical _ hz, spectralCanceledPair_eq_physicalCanonical _ _ hz,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, complexAngles, mul_pow]
  ring

theorem canonical_density_eq_physicalCanonical {N : ℕ} {lam : ℝ} {z : ℂ}
    (q : Fin N → ℝ) (hz : z ∉ spectralSetF002 lam) :
    canonicalAngularDensityF002 lam z q =
      (spectralS z * Complex.sqrt (spectralRatioF002 lam z)) ^ N *
        physicalCanonicalDensity lam (z, complexAngles q) := by
  rw [canonicalAngularDensityF002, fullRootNumerator_eq_physicalCanonical q hz]
  simp only [physicalCanonicalDensity, complexAngles, physicalComplexRoot_real _ hz]
  ring

theorem canonical_coefficient_eq_physicalCanonical (n : ℕ) {lam : ℝ} {z : ℂ}
    (hz : z ∉ spectralSetF002 lam) :
    canonicalAngularCoefficientF002 lam n z =
      (spectralS z * Complex.sqrt (spectralRatioF002 lam z)) ^ (n + 1) *
        physicalCanonicalCoefficient lam n z := by
  unfold canonicalAngularCoefficientF002 physicalCanonicalCoefficient
  simp_rw [canonical_density_eq_physicalCanonical _ hz]
  rw [integral_const_mul]
  ring

end
end IsingBulk.AnisoF002.RegularTail.C03
