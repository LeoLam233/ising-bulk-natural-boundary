import IsingBulk.AnisoF002.C03.IsotropicConstrainedCurrent

/-!
# Freezing the actual physical product phase

The scalar transport derivative uses the original real angles and the
constructed angular velocity. Its action on the actual physical phase
is derived from the exact coordinate transport and angular constraint.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Filter

variable {ι : Type*} [Fintype ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def scalarTransportDerivative (V : ι → E → ℂ) (e : ι → E) (a : E)
    (f : E → ℂ) (x : E) : ℂ :=
  scalarPartial f a x - ∑ i, V i x * scalarPartial f (e i) x

theorem scalarTransportDerivative_sum (V : ι → E → ℂ) (e : ι → E) (a x : E)
    {κ : Type*} [Fintype κ] (f : κ → E → ℂ)
    (hf : ∀ k, DifferentiableAt ℝ (f k) x) :
    scalarTransportDerivative V e a (fun y => ∑ k, f k y) x =
      ∑ k, scalarTransportDerivative V e a (f k) x := by
  simp only [scalarTransportDerivative, scalarPartial_sum _ _ _ hf, Finset.mul_sum,
    Finset.sum_sub_distrib]
  rw [Finset.sum_comm]

theorem scalarTransportDerivative_sub (V : ι → E → ℂ) (e : ι → E) (a x : E)
    (f g : E → ℂ) (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    scalarTransportDerivative V e a (fun y => f y - g y) x =
      scalarTransportDerivative V e a f x - scalarTransportDerivative V e a g x := by
  simp only [scalarTransportDerivative, scalarPartial_sub _ _ _ _ hf hg,
    mul_sub, Finset.sum_sub_distrib]
  ring

theorem scalarTransportDerivative_mul (V : ι → E → ℂ) (e : ι → E) (a x : E)
    (f g : E → ℂ) (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    scalarTransportDerivative V e a (fun y => f y * g y) x =
      scalarTransportDerivative V e a f x * g x + f x * scalarTransportDerivative V e a g x := by
  simp only [scalarTransportDerivative, scalarPartial_mul _ _ _ _ hf hg, mul_add,
    Finset.sum_add_distrib]
  have he : (∑ i, V i x * (f x * scalarPartial g (e i) x)) =
      f x * ∑ i, V i x * scalarPartial g (e i) x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have he' : (∑ i, V i x * (scalarPartial f (e i) x * g x)) =
      (∑ i, V i x * scalarPartial f (e i) x) * g x := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, he']
  ring

theorem scalarTransportDerivative_comp (V : ι → E → ℂ) (e : ι → E) (a x : E)
    (f : E → ℂ) (g : ℂ → ℂ) (g' : ℂ)
    (hf : DifferentiableAt ℝ f x) (hg : HasDerivAt g g' (f x)) :
    scalarTransportDerivative V e a (g ∘ f) x =
      g' * scalarTransportDerivative V e a f x := by
  have hc := hg.comp_hasFDerivAt x hf.hasFDerivAt
  have hp (v : E) : scalarPartial (g ∘ f) v x = g' * scalarPartial f v x := by
    rw [scalarPartial, hc.fderiv]
    rfl
  simp only [scalarTransportDerivative, hp]
  rw [mul_sub, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

def realAngularSum (q : ℂ × (ι → ℝ)) : ℂ := ∑ i, (q.2 i : ℂ)

def realAngularSumLinear : (ℂ × (ι → ℝ)) →L[ℝ] ℂ :=
  ∑ i, Complex.ofRealCLM.comp ((ContinuousLinearMap.proj i).comp
    (ContinuousLinearMap.snd ℝ ℂ (ι → ℝ)))

theorem realAngularSumLinear_apply (q : ℂ × (ι → ℝ)) :
    realAngularSumLinear q = realAngularSum q := by
  simp only [realAngularSumLinear, sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, realAngularSum, Complex.ofRealCLM_apply]
  rfl

theorem realAngularSum_differentiableAt (q : ℂ × (ι → ℝ)) :
    DifferentiableAt ℝ realAngularSum q := by
  rw [← funext realAngularSumLinear_apply]
  exact realAngularSumLinear.differentiableAt

theorem realAngularSum_timePartial (q : ℂ × (ι → ℝ)) :
    scalarPartial realAngularSum actualTimeDirection q = 0 := by
  rw [← funext realAngularSumLinear_apply, scalarPartial, ContinuousLinearMap.fderiv,
    realAngularSumLinear_apply]
  simp [realAngularSum, actualTimeDirection]

variable [DecidableEq ι]

theorem realAngularSum_angularPartial (q : ℂ × (ι → ℝ)) (i : ι) :
    scalarPartial realAngularSum (actualAngularDirection i) q = 1 := by
  rw [← funext realAngularSumLinear_apply, scalarPartial, ContinuousLinearMap.fderiv,
    realAngularSumLinear_apply]
  simp [realAngularSum, actualAngularDirection, ← Complex.ofReal_sum]

def actualTotalPhase (η τ ξ : ℝ) (q : ℂ × (ι → ℝ)) : ℂ :=
  ∑ i, actualPhysicalPhase η τ ξ q i

omit [DecidableEq ι] in
theorem actualTotalPhase_eq_coordinates (η τ ξ : ℝ) (q : ℂ × (ι → ℝ)) :
    actualTotalPhase η τ ξ q =
      (∑ i, actualPhysicalCoordinate η τ ξ i q) - realAngularSum q := by
  have he (i : ι) : actualPhysicalPhase η τ ξ q i =
      actualPhysicalCoordinate η τ ξ i q - actualHomotopyAngle η τ ξ q.2 i := by
    simp [actualPhysicalPhase, actualPhysicalCoordinate, physicalRegularCoordinate]
  simp only [actualTotalPhase, he, Finset.sum_sub_distrib]
  have hw := balancedHomotopyCoordinate_sum τ ξ q.2
    (fun i => upperPeriodicBump η (q.2 i)) (fun i => lowerPeriodicBump η (q.2 i))
  have hs : (∑ i, actualHomotopyAngle η τ ξ q.2 i) = realAngularSum q := by
    simpa only [actualHomotopyAngle, realAngularSum, Complex.ofReal_sum] using hw
  rw [hs]

omit [DecidableEq ι] in
theorem actualTotalPhase_differentiableAt (η τ ξ : ℝ) (q : ℂ × (ι → ℝ))
    (hχ : ∀ i, ContDiffAt ℝ 2 (actualPhysicalCoordinate η τ ξ i) q) :
    DifferentiableAt ℝ (actualTotalPhase η τ ξ) q := by
  rw [funext (actualTotalPhase_eq_coordinates η τ ξ)]
  exact (DifferentiableAt.fun_sum (fun i _ => (hχ i).differentiableAt (by norm_num))).sub
    (realAngularSum_differentiableAt q)

/-- The actual transport derivative freezes the physical total phase.
Both sums used here are the actual covariance and angular sums. -/
theorem actualTotalPhase_transport_zero (η τ ξ : ℝ) (q : ℂ × (ι → ℝ))
    (hχ : ∀ i, ContDiffAt ℝ 2 (actualPhysicalCoordinate η τ ξ i) q)
    (hdet : actualCoordinateDeterminant η τ ξ q ≠ 0)
    (htangent : (∑ i, actualCovarianceAngularVelocity η τ ξ i q) = 0) :
    scalarTransportDerivative (actualCovarianceAngularVelocity η τ ξ) actualAngularDirection
      actualTimeDirection (actualTotalPhase η τ ξ) q = 0 := by
  let V : ι → (ℂ × (ι → ℝ)) → ℂ := actualCovarianceAngularVelocity η τ ξ
  have hdiff (i : ι) : DifferentiableAt ℝ (actualPhysicalCoordinate η τ ξ i) q :=
    (hχ i).differentiableAt (by norm_num)
  have hs : scalarTransportDerivative V actualAngularDirection actualTimeDirection
      realAngularSum q = -(∑ i, V i q) := by
    simp only [scalarTransportDerivative, realAngularSum_timePartial,
      realAngularSum_angularPartial, mul_one, zero_sub]
  have hi (i : ι) : scalarTransportDerivative V actualAngularDirection actualTimeDirection
      (actualPhysicalCoordinate η τ ξ i) q = actualCovarianceRegularField η τ ξ i q := by
    simpa only [scalarTransportDerivative, scalarTransportVelocity, scalarCoordinateMatrix,
      V, actualCovarianceAngularVelocity, mul_comm] using congrFun (constructedAngularVelocity_transport
      (actualPhysicalCoordinate η τ ξ) actualAngularDirection actualTimeDirection q
      (actualCovarianceRegularField η τ ξ) hdet) i
  rw [funext (actualTotalPhase_eq_coordinates η τ ξ)]
  rw [scalarTransportDerivative_sub _ _ _ _ _ _
    (DifferentiableAt.fun_sum (fun i _ => hdiff i)) (realAngularSum_differentiableAt q),
    scalarTransportDerivative_sum _ _ _ _ _ hdiff]
  change (∑ i, scalarTransportDerivative V actualAngularDirection actualTimeDirection
    (actualPhysicalCoordinate η τ ξ i) q) -
      scalarTransportDerivative V actualAngularDirection actualTimeDirection realAngularSum q = 0
  simp only [hi, hs]
  rw [show (∑ i, actualCovarianceRegularField η τ ξ i q) = 0 from rightCovarianceField_sum _ _,
    show (∑ i, V i q) = 0 from htangent]
  simp

end IsingBulk.AnisoF002.Isotropic
