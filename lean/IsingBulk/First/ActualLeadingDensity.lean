import IsingBulk.First.ActualVandermonde
import IsingBulk.First.MeanShapeDensity
import IsingBulk.First.MeanRootBridge
import IsingBulk.First.FirstCoefficient

/-! Exact factorization of the actual post-mean density, including the
coincidence locus. The real sinc factor is independent of the source parameter. -/
namespace IsingBulk.First
noncomputable section
open Complex
open scoped BigOperators

theorem pairProduct_eq_strictPairs {N : ℕ} (z : Fin N → ℂ) :
    pairProduct z = ∏ p ∈ firstStrictPairs N, pairKernel (z p.1) (z p.2) := by
  simp [pairProduct, firstStrictPairs, Finset.prod_filter, Fintype.prod_prod_type]

def actualSincFactor {n : ℕ} (t : Fin n → ℝ) : ℝ :=
  ∏ p ∈ firstStrictPairs (n+1), Real.sinc ((shapeExtend t p.1-shapeExtend t p.2)/2)^2

/-- The genuine regular branch/rational numerator after pair cancellation.
No division by coordinate differences is used. -/
def actualRegularFactor {n : ℕ} (s : ℂ) (alpha : ℝ) (t : Fin n → ℝ) : ℂ :=
  ((shapeZProduct s alpha t)⁻¹+1) *
    (∏ p ∈ firstStrictPairs (n+1),
      shapeZ s alpha t p.1 * shapeZ s alpha t p.2 /
        (1-shapeZ s alpha t p.1*shapeZ s alpha t p.2)^2) *
    (∏ j, residueFactor (shapeZ s alpha t j)) *
    (∏ j, shapeY alpha t j/(2*(Real.pi:ℂ)))

theorem shapeZ_source_quadratic {n : ℕ} (s : ℂ) (alpha : ℝ) (t : Fin n → ℝ)
    (j : Fin (n+1)) :
    (shapeZ s alpha t j)^2 -
      (2*sourceS s-shapeY alpha t j-(shapeY alpha t j)⁻¹)*shapeZ s alpha t j+1=0 := by
  have h := phaseRoot_quadratic (sourceW s (shapeY alpha t j))
  unfold shapeZ sourceW at *
  linear_combination h

theorem actual_pair_cancellation {n : ℕ} (s : ℂ) (alpha : ℝ) (t : Fin n → ℝ)
    (i j : Fin (n+1))
    (hy : 1-shapeY alpha t i*shapeY alpha t j ≠ 0)
    (hz : 1-shapeZ s alpha t i*shapeZ s alpha t j ≠ 0) :
    pairKernel (shapeZ s alpha t i) (shapeZ s alpha t j) *
      pairKernel (shapeY alpha t i) (shapeY alpha t j) =
      ((shapeExtend t i-shapeExtend t j:ℝ):ℂ)^2 *
      (Real.sinc ((shapeExtend t i-shapeExtend t j)/2):ℂ)^2 *
      (shapeZ s alpha t i*shapeZ s alpha t j /
        (1-shapeZ s alpha t i*shapeZ s alpha t j)^2) := by
  rw [source_pair_identity (a := shapeY alpha t i) (b := shapeY alpha t j)
    (z := shapeZ s alpha t i) (w := shapeZ s alpha t j)
    (by exact exp_ne_zero _) (by exact exp_ne_zero _)
    (phaseRoot_ne_zero _) (phaseRoot_ne_zero _)
    (shapeZ_source_quadratic s alpha t i) (shapeZ_source_quadratic s alpha t j) hy hz]
  have h := angular_pair_squared (shapeExtend t i-alpha) (shapeExtend t j-alpha)
  have hd : shapeExtend t i-alpha-(shapeExtend t j-alpha) = shapeExtend t i-shapeExtend t j := by ring
  rw [hd] at h
  simp only [ofReal_sub] at h
  change -(_-_)^2/(_*_) = _ at h
  calc
    _ = (-(shapeY alpha t i-shapeY alpha t j)^2 /
        (shapeY alpha t i*shapeY alpha t j)) *
        (shapeZ s alpha t i*shapeZ s alpha t j /
          (1-shapeZ s alpha t i*shapeZ s alpha t j)^2) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by rw [show -(shapeY alpha t i-shapeY alpha t j)^2 /
        (shapeY alpha t i*shapeY alpha t j) =
        ((shapeExtend t i-shapeExtend t j:ℝ):ℂ)^2 *
          (Real.sinc ((shapeExtend t i-shapeExtend t j)/2):ℂ)^2 from by
            simpa only [shapeY, ofReal_sub] using h]

theorem actualSincFactor_zero (n : ℕ) : actualSincFactor (0 : Fin n → ℝ) = 1 := by
  have he : shapeExtend (0 : Fin n → ℝ) = 0 := by
    ext j
    refine Fin.lastCases ?_ (fun i => ?_) j <;> simp
  simp [actualSincFactor, he]

@[fun_prop] theorem continuous_shapeExtend_eval {n : ℕ} (j : Fin (n+1)) :
    Continuous (fun t : Fin n → ℝ => shapeExtend t j) := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [shapeExtend_last]
    fun_prop
  · simp only [shapeExtend_castSucc]
    fun_prop

theorem actualSincFactor_continuous (n : ℕ) : Continuous (@actualSincFactor n) := by
  unfold actualSincFactor
  apply continuous_finsetProd
  intro p _
  exact (Real.continuous_sinc.comp (by fun_prop)).pow 2

/-- Exact factorization of the physical numerator, valid also on all
coordinate-coincidence hyperplanes. Only its genuine rational poles are excluded. -/
theorem shapeRegularNumerator_factorization {n : ℕ} (s : ℂ) (alpha : ℝ) (t : Fin n → ℝ)
    (hy : ∀ i j : Fin (n+1), i < j → 1-shapeY alpha t i*shapeY alpha t j ≠ 0)
    (hz : ∀ i j : Fin (n+1), i < j → 1-shapeZ s alpha t i*shapeZ s alpha t j ≠ 0) :
    shapeRegularNumerator s alpha t =
      (firstVandermonde (shapeExtend t):ℂ)^2 * (actualSincFactor t:ℂ) *
        actualRegularFactor s alpha t := by
  have hp : pairProduct (shapeZ s alpha t) * pairProduct (shapeY alpha t) =
      (firstVandermonde (shapeExtend t):ℂ)^2 * (actualSincFactor t:ℂ) *
        (∏ p ∈ firstStrictPairs (n+1), shapeZ s alpha t p.1*shapeZ s alpha t p.2 /
          (1-shapeZ s alpha t p.1*shapeZ s alpha t p.2)^2) := by
    rw [pairProduct_eq_strictPairs, pairProduct_eq_strictPairs, ← Finset.prod_mul_distrib]
    calc
      _ = ∏ p ∈ firstStrictPairs (n+1),
          ((shapeExtend t p.1-shapeExtend t p.2:ℝ):ℂ)^2 *
          (Real.sinc ((shapeExtend t p.1-shapeExtend t p.2)/2):ℂ)^2 *
          (shapeZ s alpha t p.1*shapeZ s alpha t p.2 /
            (1-shapeZ s alpha t p.1*shapeZ s alpha t p.2)^2) := by
        apply Finset.prod_congr rfl
        intro p hp
        exact actual_pair_cancellation s alpha t p.1 p.2
          (hy _ _ ((mem_firstStrictPairs p).mp hp))
          (hz _ _ ((mem_firstStrictPairs p).mp hp))
      _ = _ := by
        simp only [Finset.prod_mul_distrib]
        simp [firstVandermonde, actualSincFactor, ← Finset.prod_pow]
  unfold shapeRegularNumerator actualRegularFactor
  rw [show ((shapeZProduct s alpha t)⁻¹+1) * pairProduct (shapeZ s alpha t) *
      pairProduct (shapeY alpha t) = ((shapeZProduct s alpha t)⁻¹+1) *
        (pairProduct (shapeZ s alpha t)*pairProduct (shapeY alpha t)) by ring, hp]
  ring

theorem postMeanDensity_factorization {n : ℕ} (s : ℂ) (alpha : ℝ) (t : Fin n → ℝ)
    (hy : ∀ i j : Fin (n+1), i < j → 1-shapeY alpha t i*shapeY alpha t j ≠ 0)
    (hz : ∀ i j : Fin (n+1), i < j → 1-shapeZ s alpha t i*shapeZ s alpha t j ≠ 0) :
    postMeanDensity s alpha t =
      2*(Real.pi:ℂ) * (firstVandermonde (shapeExtend t):ℂ)^2 *
        (actualSincFactor t:ℂ) * actualRegularFactor s alpha t /
          shapePoleDenominator s alpha t := by
  rw [postMeanDensity, shapeRegularNumerator_factorization s alpha t hy hz]
  ring

end
end IsingBulk.First
