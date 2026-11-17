import IsingBulk.AnisoF002.C03.IsotropicPhaseTransport

/-!
# The physical product kernel stays unchanged under the exact current

The phase expression is identified with the full product of actual
interior roots. Both signs have a nonzero denominator on the physical
homotopy. The exact current then differentiates only the transported
amplitude, including its parameter dependence and smooth real cutoffs.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric

def physicalPhaseKernel (σ z : ℂ) : ℂ :=
  (1 + σ * Complex.exp (-(z * Complex.I))) / (1 - σ * Complex.exp (-(z * Complex.I)))

theorem physicalPhaseKernel_analyticAt (σ z : ℂ)
    (hden : 1 - σ * Complex.exp (-(z * Complex.I)) ≠ 0) :
    AnalyticAt ℂ (physicalPhaseKernel σ) z := by
  have he : AnalyticAt ℂ (fun w => Complex.exp (-(w * Complex.I))) z :=
    analyticAt_cexp.comp ((analyticAt_id.mul analyticAt_const).neg)
  exact (analyticAt_const.add (analyticAt_const.mul he)).div
    (analyticAt_const.sub (analyticAt_const.mul he)) hden

variable {ι : Type*} [Fintype ι]

def actualSignedProductKernel (σ : ℂ) (η τ ξ : ℝ) (q : ℂ × (ι → ℝ)) : ℂ :=
  physicalPhaseKernel σ (actualTotalPhase η τ ξ q)

theorem actualTotalPhase_exp_product (η τ ξ : ℝ) (q : ℂ × (ι → ℝ)) :
    Complex.exp (-(actualTotalPhase η τ ξ q * Complex.I)) =
      ∏ i, isotropicInteriorRoot (q.1, actualHomotopyAngle η τ ξ q.2 i) := by
  have he : -(actualTotalPhase η τ ξ q * Complex.I) =
      ∑ i, -(actualPhysicalPhase η τ ξ q i * Complex.I) := by
    simp only [actualTotalPhase, Finset.sum_neg_distrib, Finset.sum_mul]
  rw [he, Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  exact upperPhysicalPhase_exp _

/-- Exact identification with the complete signed physical root product. -/
theorem actualSignedProductKernel_eq_physical (σ : ℂ) (η τ ξ : ℝ) (q : ℂ × (ι → ℝ)) :
    actualSignedProductKernel σ η τ ξ q =
      (1 + σ * ∏ i, isotropicInteriorRoot (q.1, actualHomotopyAngle η τ ξ q.2 i)) /
        (1 - σ * ∏ i, isotropicInteriorRoot (q.1, actualHomotopyAngle η τ ξ q.2 i)) := by
  rw [actualSignedProductKernel, physicalPhaseKernel, actualTotalPhase_exp_product]

theorem actualSignedProductKernel_denominator [Nonempty ι]
    (σ : ℂ) (hσ : ‖σ‖ ≤ 1) (η τ ξ : ℝ) (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ)
    (q : ℂ × (ι → ℝ)) (hq : 0 < q.1.im) :
    1 - σ * Complex.exp (-(actualTotalPhase η τ ξ q * Complex.I)) ≠ 0 := by
  rw [actualTotalPhase_exp_product]
  exact balancedHomotopy_product_denominator q.1 hq σ hσ τ ξ hτ hξ q.2
    (fun i => upperPeriodicBump η (q.2 i)) (fun i => lowerPeriodicBump η (q.2 i))
    (fun i => (upperPeriodicBump_bounds η (q.2 i)).1)
    (fun i => (lowerPeriodicBump_bounds η (q.2 i)).1)
    (fun i => (actual_bump_sine_signs hη (q.2 i)).1)
    (fun i => (actual_bump_sine_signs hη (q.2 i)).2)

variable [DecidableEq ι]

theorem actualSignedProductKernel_transport [Nonempty ι]
    (σ : ℂ) (hσ : ‖σ‖ ≤ 1) (η τ ξ : ℝ) (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ)
    (q : ℂ × (ι → ℝ)) (hq : 0 < q.1.im)
    (hχ : ∀ i, ContDiffAt ℝ 2 (actualPhysicalCoordinate η τ ξ i) q)
    (hdet : actualCoordinateDeterminant η τ ξ q ≠ 0)
    (htangent : (∑ i, actualCovarianceAngularVelocity η τ ξ i q) = 0) :
    DifferentiableAt ℝ (actualSignedProductKernel σ η τ ξ) q ∧
      scalarTransportDerivative (actualCovarianceAngularVelocity η τ ξ) actualAngularDirection
        actualTimeDirection (actualSignedProductKernel σ η τ ξ) q = 0 := by
  have hd := actualSignedProductKernel_denominator σ hσ η τ ξ hη hτ hξ q hq
  have hg := physicalPhaseKernel_analyticAt σ (actualTotalPhase η τ ξ q) hd
  have hφ := actualTotalPhase_differentiableAt η τ ξ q hχ
  refine ⟨hg.restrictScalars.differentiableAt.comp q hφ, ?_⟩
  have hc := scalarTransportDerivative_comp (actualCovarianceAngularVelocity η τ ξ)
    actualAngularDirection actualTimeDirection q (actualTotalPhase η τ ξ) (physicalPhaseKernel σ)
    _ hφ hg.differentiableAt.hasDerivAt
  rw [actualTotalPhase_transport_zero η τ ξ q hχ hdet htangent, mul_zero] at hc
  exact hc

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def regularTransportAmplitude (χ : ι → E → ℂ) (e : ι → E) (a : E)
    (B : ι → E → ℂ) (b : E → ℂ) (x : E) : ℂ :=
  scalarRegularParameterDerivative χ e a b x +
    (∑ i, B i x * scalarRegularFrameDerivative χ e b i x) +
    (∑ i, scalarRegularFrameDerivative χ e (B i) i x) * b x

/-- If the constructed transport freezes K, its exact current leaves
K unchanged and transports the entire parameter-dependent amplitude. -/
theorem exact_constructed_frozen_current (χ : ι → E → ℂ) (e : ι → E) (a x : E)
    (B : ι → E → ℂ) (K b : E → ℂ)
    (hχ : ∀ i, ContDiffAt ℝ 2 (χ i) x)
    (hB : ∀ i, DifferentiableAt ℝ (B i) x)
    (hK : DifferentiableAt ℝ K x) (hb : DifferentiableAt ℝ b x)
    (hdet : scalarCoordinateDet χ e x ≠ 0)
    (hfreeze : scalarTransportDerivative (constructedAngularVelocity χ e a B) e a K x = 0) :
    scalarPartial (fun y => scalarCoordinateDet χ e y * (K y * b y)) a x -
        (∑ i, scalarPartial (fun y => constructedAngularVelocity χ e a B i y *
          scalarCoordinateDet χ e y * (K y * b y)) (e i) x) =
      scalarCoordinateDet χ e x * K x * regularTransportAmplitude χ e a B b x := by
  let V := constructedAngularVelocity χ e a B
  have hV := constructedAngularVelocity_differentiableAt χ e a x B hχ hB hdet
  have hk := exact_scalar_current χ e a x V (fun y => K y * b y) hχ hV (hK.mul hb) hdet
  change _ = scalarCoordinateDet χ e x *
    (scalarTransportDerivative V e a (fun y => K y * b y) x + scalarTransportDivergence χ e a V x *
      (K x * b x)) at hk
  rw [scalarTransportDerivative_mul V e a x K b hK hb, hfreeze, zero_mul, zero_add] at hk
  have h0 := exact_scalar_current χ e a x V b hχ hV hb hdet
  have hr := exact_constructed_regular_current χ e a x B b hχ hB hb hdet
  have he : scalarCoordinateDet χ e x *
      (scalarTransportDerivative V e a b x + scalarTransportDivergence χ e a V x * b x) =
      scalarCoordinateDet χ e x * regularTransportAmplitude χ e a B b x := h0.symm.trans hr
  calc
    _ = K x * (scalarCoordinateDet χ e x *
        (scalarTransportDerivative V e a b x + scalarTransportDivergence χ e a V x * b x)) :=
      hk.trans (by ring)
    _ = K x * (scalarCoordinateDet χ e x * regularTransportAmplitude χ e a B b x) :=
      congrArg (fun z => K x * z) he
    _ = _ := by ring

end IsingBulk.AnisoF002.Isotropic
