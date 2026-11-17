import IsingBulk.AnisoF002.C03.IsotropicInverseEntryJets
import IsingBulk.AnisoF002.C03.IsotropicCutoffCoefficient
import IsingBulk.AnisoF002.C03.IsotropicAnalyticFramePullback

/-!
# Exact separation of analytic transport and real cutoff transport

Each transport step acts on a product of an analytic regular-coordinate
factor and a smooth function of the original real angles. The latter is
differentiated through the full balanced inverse; it is never continued
to complex angles.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators Matrix
open Set

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem regularTransportAmplitude_eq_transport (χ : ι → E → ℂ) (e : ι → E) (a x : E)
    (B : ι → E → ℂ) (b : E → ℂ) (hdet : scalarCoordinateDet χ e x ≠ 0) :
    regularTransportAmplitude χ e a B b x =
      scalarTransportDerivative (constructedAngularVelocity χ e a B) e a b x +
        (∑ i, scalarRegularFrameDerivative χ e (B i) i x) * b x := by
  have ht := scalar_frame_transport_algebra (scalarCoordinateMatrix χ e x)
    (fun i => scalarPartial (χ i) a x) (fun i => constructedAngularVelocity χ e a B i x)
    (fun i => B i x) (fun i => scalarPartial b (e i) x) (scalarPartial b a x) hdet
    (constructedAngularVelocity_transport χ e a x B hdet).symm
  change scalarTransportDerivative (constructedAngularVelocity χ e a B) e a b x =
    scalarRegularParameterDerivative χ e a b x +
      ∑ i, B i x * scalarRegularFrameDerivative χ e b i x at ht
  rw [regularTransportAmplitude, ← ht]

theorem regularTransportAmplitude_mul (χ : ι → E → ℂ) (e : ι → E) (a x : E)
    (B : ι → E → ℂ) (f g : E → ℂ)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (hdet : scalarCoordinateDet χ e x ≠ 0) :
    regularTransportAmplitude χ e a B (fun y => f y * g y) x =
      regularTransportAmplitude χ e a B f x * g x +
        f x * scalarTransportDerivative (constructedAngularVelocity χ e a B) e a g x := by
  rw [regularTransportAmplitude_eq_transport χ e a x B _ hdet,
    regularTransportAmplitude_eq_transport χ e a x B f hdet,
    scalarTransportDerivative_mul _ e a x f g hf hg]
  ring

theorem regularTransportAmplitude_sum (χ : ι → E → ℂ) (e : ι → E) (a x : E)
    (B : ι → E → ℂ) {κ : Type*} [Fintype κ] (f : κ → E → ℂ)
    (hf : ∀ k, DifferentiableAt ℝ (f k) x)
    (hdet : scalarCoordinateDet χ e x ≠ 0) :
    regularTransportAmplitude χ e a B (fun y => ∑ k, f k y) x =
      ∑ k, regularTransportAmplitude χ e a B (f k) x := by
  simp only [regularTransportAmplitude_eq_transport χ e a x B _ hdet,
    scalarTransportDerivative_sum _ e a x f hf, Finset.mul_sum, Finset.sum_add_distrib]

def realAngularPartial {N : ℕ} (g : (Fin N → ℝ) → ℂ) (i : Fin N) : (Fin N → ℝ) → ℂ :=
  scalarPartial g (Pi.single i 1)

theorem realAngularPartial_jet_control {N k : ℕ} (g : (Fin N → ℝ) → ℂ) (i : Fin N)
    (C : ℝ) (hg : FiniteJetControl (k + 1) g C) :
    FiniteJetControl k (realAngularPartial g i) C := by
  exact hg.scalarPartial _ (by simp only [Pi.norm_single, norm_one, le_refl])

theorem scalarPartial_real_angular_lift {N : ℕ} (g : (Fin N → ℝ) → ℂ)
    (x v : ℂ × (Fin N → ℝ)) (hg : DifferentiableAt ℝ g x.2) :
    scalarPartial (fun y : ℂ × (Fin N → ℝ) => g y.2) v x = fderiv ℝ g x.2 v.2 := by
  have hh := hg.hasFDerivAt.comp x (hasFDerivAt_snd (p := x))
  simp only [Function.comp_def] at hh
  rw [scalarPartial, hh.fderiv]
  rfl

theorem scalarTransportDerivative_angular_lift {N : ℕ}
    (V : Fin N → (ℂ × (Fin N → ℝ)) → ℂ) (g : (Fin N → ℝ) → ℂ)
    (x : ℂ × (Fin N → ℝ)) (hg : DifferentiableAt ℝ g x.2) :
    scalarTransportDerivative V actualAngularDirection actualTimeDirection
      (fun y => g y.2) x = -∑ i, V i x * realAngularPartial g i x.2 := by
  rw [scalarTransportDerivative]
  simp_rw [scalarPartial_real_angular_lift g x _ hg]
  simp only [actualTimeDirection, actualAngularDirection, map_zero, zero_sub,
    realAngularPartial, scalarPartial]

theorem actualCovarianceAngularVelocity_inverse_entries {N : ℕ} (η τ ξ : ℝ)
    (q : ℂ × (Fin N → ℝ))
    (hq : ∀ i, 0 < (isotropicDispersion (q.1, actualHomotopyAngle η τ ξ q.2 i)).im)
    (hdet : actualCoordinateDeterminant η τ ξ q ≠ 0)
    (hdata : ∀ i,
      AnalyticAt ℂ explicitRightInverse (q.1, actualPhysicalCoordinate η τ ξ i q) ∧
      Complex.cos (actualPhysicalCoordinate η τ ξ i q / 2) ≠ 0 ∧
      explicitRightDenominator (q.1, actualPhysicalCoordinate η τ ξ i q) ≠ 0 ∧
      explicitRightInverse (q.1, actualPhysicalCoordinate η τ ξ i q) =
        actualHomotopyAngle η τ ξ q.2 i)
    (hnear : ‖actualBalancedOperator η τ ξ q.2 - 1‖ ≤ (1 / 2 : ℝ)) (i : Fin N) :
    actualCovarianceAngularVelocity η τ ξ i q =
      -∑ j, actualBalancedInverseEntry η τ ξ i j q.2 *
        rightCutoffTransportCoefficient (regularJointMap (actualPhysicalCoordinate η τ ξ) q) j := by
  let V : Fin N → ℂ := fun j => actualCovarianceAngularVelocity η τ ξ j q
  let K : Fin N → ℂ := fun j =>
    rightCutoffTransportCoefficient (regularJointMap (actualPhysicalCoordinate η τ ξ) q) j
  have ht : actualBalancedOperator η τ ξ q.2 V = -K :=
    actualCovarianceAngularVelocity_balanced η τ ξ q hq hdet hdata
  have hi := (actualBalancedOperator_inverse_identity η τ ξ q.2 hnear).2
  have he : V = -(actualBalancedInverseOperator η τ ξ q.2) K := by
    calc
      V = (actualBalancedInverseOperator η τ ξ q.2)
          (actualBalancedOperator η τ ξ q.2 V) := by
        change V = (actualBalancedInverseOperator η τ ξ q.2 *
          actualBalancedOperator η τ ξ q.2) V
        rw [hi]
        rfl
      _ = (actualBalancedInverseOperator η τ ξ q.2) (-K) := congrArg _ ht
      _ = _ := map_neg _ _
  have hei := congrFun he i
  rw [Pi.neg_apply, angularOperator_apply_eq_sum] at hei
  exact hei

theorem actualTransport_separated_product {N : ℕ} (η τ ξ : ℝ)
    (F : RegularJointSpace N → ℂ) (g : (Fin N → ℝ) → ℂ)
    (x : ℂ × (Fin N → ℝ))
    (hχ : ∀ i, DifferentiableAt ℝ (actualPhysicalCoordinate η τ ξ i) x)
    (hB : DifferentiableAt ℂ (fun p : RegularJointSpace N => rightCovarianceField p.1 p.2)
      (regularJointMap (actualPhysicalCoordinate η τ ξ) x))
    (hF : DifferentiableAt ℂ F (regularJointMap (actualPhysicalCoordinate η τ ξ) x))
    (hg : DifferentiableAt ℝ g x.2)
    (hdet : actualCoordinateDeterminant η τ ξ x ≠ 0)
    (hV : ∀ i, actualCovarianceAngularVelocity η τ ξ i x =
      -∑ j, actualBalancedInverseEntry η τ ξ i j x.2 *
        rightCutoffTransportCoefficient (regularJointMap (actualPhysicalCoordinate η τ ξ) x) j) :
    actualTransportAmplitude η τ ξ
      (fun y => F (regularJointMap (actualPhysicalCoordinate η τ ξ) y) * g y.2) x =
      analyticTransportAmplitude (fun p : RegularJointSpace N => rightCovarianceField p.1 p.2) F
        (regularJointMap (actualPhysicalCoordinate η τ ξ) x) * g x.2 +
      ∑ i, ∑ j,
        (F (regularJointMap (actualPhysicalCoordinate η τ ξ) x) *
          rightCutoffTransportCoefficient (regularJointMap (actualPhysicalCoordinate η τ ξ) x) j) *
          (actualBalancedInverseEntry η τ ξ i j x.2 * realAngularPartial g i x.2) := by
  have hm : DifferentiableAt ℝ (regularJointMap (actualPhysicalCoordinate η τ ξ)) x :=
    differentiableAt_fst.prodMk (differentiableAt_pi.mpr hχ)
  have hFp : DifferentiableAt ℝ
      (fun y => F (regularJointMap (actualPhysicalCoordinate η τ ξ) y)) x :=
    (hF.restrictScalars (𝕜 := ℝ)).comp x hm
  have hgp : DifferentiableAt ℝ (fun y : ℂ × (Fin N → ℝ) => g y.2) x :=
    hg.comp x differentiableAt_snd
  rw [actualTransportAmplitude, regularTransportAmplitude_mul _ _ _ _ _ _ _ hFp hgp hdet]
  have ht := regularTransportAmplitude_joint_pullback (actualPhysicalCoordinate η τ ξ)
    (fun p : RegularJointSpace N => rightCovarianceField p.1 p.2) F x hχ hB hF hdet
  change regularTransportAmplitude (actualPhysicalCoordinate η τ ξ) actualAngularDirection
    actualTimeDirection (actualCovarianceRegularField η τ ξ)
    (fun y => F (regularJointMap (actualPhysicalCoordinate η τ ξ) y)) x = _ at ht
  rw [ht, scalarTransportDerivative_angular_lift _ g x hg]
  change _ + _ * (-∑ i, actualCovarianceAngularVelocity η τ ξ i x * _) = _
  simp_rw [hV]
  simp only [neg_mul, Finset.sum_neg_distrib, neg_neg, Finset.sum_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end IsingBulk.AnisoF002.Isotropic
