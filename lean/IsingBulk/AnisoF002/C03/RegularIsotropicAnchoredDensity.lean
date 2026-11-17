import IsingBulk.AnisoF002.C03.RegularIsotropicAnchorFrame
import IsingBulk.AnisoF002.C03.RegularIsotropicAnchorDisks
import IsingBulk.AnisoF002.C03.IsotropicTransportSupport
import IsingBulk.AnisoF002.C03.IsotropicFullPhysicalHomotopy

/-!
# The complete physical anchored density and its exact current

The kernel belongs to the initial analytic amplitude and is differentiated
at every step. The actual scalar coordinate determinant, full balanced
inverse, original normalization and real cutoff are all retained.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators ContDiff
open Set Filter Metric

def anchoredTransportDescendant {N : ℕ} (a : Fin N) (σ : ℂ) (η τ ξ : ℝ)
    (g : (Fin N → ℝ) → ℂ) : ℕ → (ℂ × (Fin N → ℝ)) → ℂ :=
  coordinateTransportDescendant (anchoredRegularField a) η τ ξ
    (fun q => anchoredRegularDensity σ (regularJointMap (actualPhysicalCoordinate η τ ξ) q) * g q.2)

def anchoredTransportedDensity {N : ℕ} (a : Fin N) (σ : ℂ) (η τ ξ : ℝ)
    (g : (Fin N → ℝ) → ℂ) (j : ℕ) (q : ℂ × (Fin N → ℝ)) : ℂ :=
  actualCoordinateDeterminant η τ ξ q * anchoredTransportDescendant a σ η τ ξ g j q

def anchoredTransportedFlux {N : ℕ} (a : Fin N) (σ : ℂ) (η τ ξ : ℝ)
    (g : (Fin N → ℝ) → ℂ) (j : ℕ) (i : Fin N) (q : ℂ × (Fin N → ℝ)) : ℂ :=
  actualAnchoredAngularVelocity a η τ ξ i q * anchoredTransportedDensity a σ η τ ξ g j q

theorem regularProductKernel_actual {N : ℕ} (σ : ℂ) (η τ ξ : ℝ)
    (q : ℂ × (Fin N → ℝ))
    (hU : ∀ i, explicitRightInverse (q.1, actualPhysicalCoordinate η τ ξ i q) =
      actualHomotopyAngle η τ ξ q.2 i) :
    regularProductKernel σ (regularJointMap (actualPhysicalCoordinate η τ ξ) q) =
      actualSignedProductKernel σ η τ ξ q := by
  have he : regularRootProduct (regularJointMap (actualPhysicalCoordinate η τ ξ) q) =
      ∏ i, isotropicInteriorRoot (q.1, actualHomotopyAngle η τ ξ q.2 i) :=
    Finset.prod_congr rfl (fun i _ => regularInverseRoot_actual η τ ξ q i (hU i))
  rw [actualSignedProductKernel_eq_physical, regularProductKernel, he]

theorem anchoredTransportedDensity_zero_physical {N : ℕ} (a : Fin N) (σ : ℂ) (η τ ξ : ℝ)
    (g : (Fin N → ℝ) → ℂ) (q : ℂ × (Fin N → ℝ))
    (hq : ∀ i, 0 < (isotropicDispersion (q.1, actualHomotopyAngle η τ ξ q.2 i)).im)
    (hU : ∀ i, explicitRightInverse (q.1, actualPhysicalCoordinate η τ ξ i q) =
      actualHomotopyAngle η τ ξ q.2 i)
    (hD : ∀ i, Complex.sin (actualPhysicalPhase η τ ξ q i) -
      Complex.sin (actualHomotopyAngle η τ ξ q.2 i) ≠ 0) :
    anchoredTransportedDensity a σ η τ ξ g 0 q =
      g q.2 * (actualBalancedJacobian η τ ξ q.2).det *
        isotropicBarePhysicalDensity q.1 σ (actualHomotopyAngle η τ ξ q.2) := by
  have hh := actualInitialAmplitude_physical_density σ η τ ξ (fun y => g y.2) q hq hU hD
  change actualCoordinateDeterminant η τ ξ q *
      (anchoredRegularDensity σ (regularJointMap (actualPhysicalCoordinate η τ ξ) q) * g q.2) = _
  rw [anchoredRegularDensity, regularProductKernel_actual σ η τ ξ q hU]
  unfold actualInitialAmplitude actualRegularNumerator at hh
  unfold isotropicBarePhysicalDensity
  dsimp only [regularJointMap]
  unfold actualPhysicalPhase at hh
  linear_combination hh

theorem anchoredTransportDescendant_tsupport {N : ℕ} (a : Fin N) (σ : ℂ) (η τ ξ : ℝ)
    (g : (Fin N → ℝ) → ℂ) (j : ℕ) :
    tsupport (anchoredTransportDescendant a σ η τ ξ g j) ⊆ Prod.snd ⁻¹' tsupport g := by
  apply (regularTransportDescendant_tsupport (actualPhysicalCoordinate η τ ξ) actualAngularDirection
    actualTimeDirection (actualAnchoredRegularField a η τ ξ) _ j).trans
  apply closure_minimal
  · intro q hq
    have hg : g q.2 ≠ 0 := by
      intro hz
      exact hq (by change anchoredRegularDensity σ _ * g q.2 = 0; rw [hz, mul_zero])
    exact subset_closure hg
  · exact isClosed_closure.preimage continuous_snd

theorem anchoredTransportedDensity_tsupport {N : ℕ} (a : Fin N) (σ : ℂ) (η τ ξ : ℝ)
    (g : (Fin N → ℝ) → ℂ) (j : ℕ) :
    tsupport (anchoredTransportedDensity a σ η τ ξ g j) ⊆ Prod.snd ⁻¹' tsupport g :=
  tsupport_mul_subset_right.trans (anchoredTransportDescendant_tsupport a σ η τ ξ g j)

theorem anchoredTransportedFlux_tsupport {N : ℕ} (a : Fin N) (σ : ℂ) (η τ ξ : ℝ)
    (g : (Fin N → ℝ) → ℂ) (j : ℕ) (i : Fin N) :
    tsupport (anchoredTransportedFlux a σ η τ ξ g j i) ⊆ Prod.snd ⁻¹' tsupport g :=
  tsupport_mul_subset_right.trans (anchoredTransportedDensity_tsupport a σ η τ ξ g j)

theorem anchoredTransportedDensity_zero_germ {N : ℕ} (a : Fin N) (σ : ℂ) (η τ ξ : ℝ)
    (g : (Fin N → ℝ) → ℂ) (j : ℕ) (q : ℂ × (Fin N → ℝ)) (hq : q.2 ∉ tsupport g) :
    anchoredTransportedDensity a σ η τ ξ g j =ᶠ[𝓝 q] (fun _ => 0) :=
  notMem_tsupport_iff_eventuallyEq.mp (fun h => hq (anchoredTransportedDensity_tsupport a σ η τ ξ g j h))

theorem anchoredTransportedFlux_zero_germ {N : ℕ} (a : Fin N) (σ : ℂ) (η τ ξ : ℝ)
    (g : (Fin N → ℝ) → ℂ) (j : ℕ) (i : Fin N) (q : ℂ × (Fin N → ℝ)) (hq : q.2 ∉ tsupport g) :
    anchoredTransportedFlux a σ η τ ξ g j i =ᶠ[𝓝 q] (fun _ => 0) :=
  notMem_tsupport_iff_eventuallyEq.mp (fun h => hq (anchoredTransportedFlux_tsupport a σ η τ ξ g j i h))

/-- The actual anchored current, valid also at total coincidence. All
derivatives of the full physical kernel and cutoff remain in b_(j+1). -/
theorem anchoredTransportedDensity_current {N : ℕ} (a : Fin N) (σ : ℂ) (η τ ξ : ℝ)
    (g : (Fin N → ℝ) → ℂ) (j : ℕ) (q : ℂ × (Fin N → ℝ))
    (hχ : ∀ i, ContDiffAt ℝ ∞ (actualPhysicalCoordinate η τ ξ i) q)
    (hdet : actualCoordinateDeterminant η τ ξ q ≠ 0)
    (hB : AnalyticAt ℂ (anchoredRegularField a) (regularJointMap (actualPhysicalCoordinate η τ ξ) q))
    (hF : AnalyticAt ℂ (anchoredRegularDensity σ) (regularJointMap (actualPhysicalCoordinate η τ ξ) q))
    (hg : ContDiffAt ℝ ∞ g q.2)
    (htangent : ∀ᶠ y in 𝓝 q, (∑ i, actualAnchoredAngularVelocity a η τ ξ i y) = 0) :
    ContDiffAt ℝ ∞ (anchoredTransportedDensity a σ η τ ξ g j) q ∧
      (∀ i, DifferentiableAt ℝ (anchoredTransportedFlux a σ η τ ξ g j i) q) ∧
      ∀ anchor : Fin N,
        scalarPartial (anchoredTransportedDensity a σ η τ ξ g j) actualTimeDirection q -
          (∑ i ∈ Finset.univ.erase anchor,
            scalarPartial (anchoredTransportedFlux a σ η τ ξ g j i)
              (actualAngularDirection i - actualAngularDirection anchor) q) =
          anchoredTransportedDensity a σ η τ ξ g (j + 1) q := by
  let χ := actualPhysicalCoordinate (ι := Fin N) η τ ξ
  let B := actualAnchoredRegularField a η τ ξ
  let b := anchoredTransportDescendant a σ η τ ξ g
  have hm : ContDiffAt ℝ ∞ (regularJointMap χ) q :=
    contDiffAt_fst.prodMk (contDiffAt_pi.mpr hχ)
  have hBs : ∀ i, ContDiffAt ℝ ∞ (B i) q := by
    intro i
    exact contDiffAt_pi.mp (hB.restrictScalars.contDiffAt.comp q hm) i
  have hinit : ContDiffAt ℝ ∞
      (fun y => anchoredRegularDensity σ (regularJointMap χ y) * g y.2) q :=
    (hF.restrictScalars.contDiffAt.comp q hm).mul (hg.comp q contDiffAt_snd)
  have hb : ContDiffAt ℝ ∞ (b j) q :=
    regularTransportDescendant_contDiffAt χ actualAngularDirection actualTimeDirection q B _ hχ hBs hinit hdet j
  have hχ2 (i : Fin N) := (hχ i).of_le (show (2 : ℕ∞) ≤ ∞ by simp)
  have hJ : ContDiffAt ℝ ∞ (actualCoordinateDeterminant η τ ξ) q :=
    scalarMatrixDet_contDiffAt _ q (scalarCoordinateMatrix_contDiffAt χ actualAngularDirection q hχ)
  have hdensity : ContDiffAt ℝ ∞ (anchoredTransportedDensity a σ η τ ξ g j) q := hJ.mul hb
  have hBd (i : Fin N) := (hBs i).differentiableAt (by simp)
  have hbD := hb.differentiableAt (by simp)
  have hV (i : Fin N) : DifferentiableAt ℝ (actualAnchoredAngularVelocity a η τ ξ i) q :=
    constructedAngularVelocity_differentiableAt χ actualAngularDirection actualTimeDirection q B hχ2 hBd hdet i
  have hflux (i : Fin N) : DifferentiableAt ℝ (anchoredTransportedFlux a σ η τ ξ g j i) q :=
    (hV i).mul (hdensity.differentiableAt (by simp))
  refine ⟨hdensity, hflux, ?_⟩
  intro anchor
  have ht : (fun y => ∑ i, anchoredTransportedFlux a σ η τ ξ g j i y) =ᶠ[𝓝 q] (fun _ => 0) := by
    filter_upwards [htangent] with y hy
    simp only [anchoredTransportedFlux, ← Finset.sum_mul, hy, zero_mul]
  have hdiv := tangent_current_constrained_divergence
    (anchoredTransportedFlux a σ η τ ξ g j) actualAngularDirection q anchor hflux ht
  rw [hdiv]
  have hcurrent := exact_constructed_regular_current χ actualAngularDirection actualTimeDirection q B (b j)
    hχ2 hBd hbD hdet
  change scalarPartial (fun y => scalarCoordinateDet χ actualAngularDirection y * b j y)
      actualTimeDirection q -
    (∑ i, scalarPartial (fun y => constructedAngularVelocity χ actualAngularDirection
      actualTimeDirection B i y * (scalarCoordinateDet χ actualAngularDirection y * b j y))
      (actualAngularDirection i) q) =
    scalarCoordinateDet χ actualAngularDirection q *
      regularTransportAmplitude χ actualAngularDirection actualTimeDirection B (b j) q
  simpa only [regularTransportAmplitude, mul_assoc] using hcurrent

end IsingBulk.AnisoF002.Isotropic
