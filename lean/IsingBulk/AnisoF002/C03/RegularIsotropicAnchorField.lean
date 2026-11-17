import IsingBulk.AnisoF002.C03.IsotropicCutoffCoefficient
import IsingBulk.AnisoF002.C03.IsotropicSeparatedTransport

/-!
# The actual named-anchor regular field

The field is the literal frozen inverse-slope formula. Its exact weighted
sum, full balanced inverse velocity, and tangency are proved here. The
complete product kernel is not frozen by this field and will be included
in the transported amplitude.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators Matrix
open Set Filter Metric

def anchoredRegularField {N : ℕ} (a : Fin N) (p : RegularJointSpace N) (i : Fin N) : ℂ :=
  if i = a then -(∑ j, jointParameterDerivative explicitRightInverse (p.1, p.2 j)) /
    jointCoordinateDerivative explicitRightInverse (p.1, p.2 a) else 0

def anchoredCutoffCoefficient {N : ℕ} (a : Fin N) (p : RegularJointSpace N) (i : Fin N) : ℂ :=
  jointParameterDerivative explicitRightInverse (p.1, p.2 i) +
    jointCoordinateDerivative explicitRightInverse (p.1, p.2 i) * anchoredRegularField a p i

theorem anchoredRegularField_weighted_sum {N : ℕ} (a : Fin N) (p : RegularJointSpace N)
    (ha : jointCoordinateDerivative explicitRightInverse (p.1, p.2 a) ≠ 0) :
    (∑ i, jointCoordinateDerivative explicitRightInverse (p.1, p.2 i) *
      anchoredRegularField a p i) =
      -(∑ i, jointParameterDerivative explicitRightInverse (p.1, p.2 i)) := by
  simp only [anchoredRegularField, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  exact mul_div_cancel₀ _ ha

theorem anchoredCutoffCoefficient_sum {N : ℕ} (a : Fin N) (p : RegularJointSpace N)
    (ha : jointCoordinateDerivative explicitRightInverse (p.1, p.2 a) ≠ 0) :
    (∑ i, anchoredCutoffCoefficient a p i) = 0 := by
  simp only [anchoredCutoffCoefficient, Finset.sum_add_distrib,
    anchoredRegularField_weighted_sum a p ha, add_neg_cancel]

theorem anchoredRegularField_analyticAt {N : ℕ} (a : Fin N) (p : RegularJointSpace N)
    (hU : ∀ i, AnalyticAt ℂ explicitRightInverse (p.1, p.2 i))
    (ha : jointCoordinateDerivative explicitRightInverse (p.1, p.2 a) ≠ 0) :
    AnalyticAt ℂ (anchoredRegularField a) p := by
  have hm (i : Fin N) : AnalyticAt ℂ (fun q : RegularJointSpace N => (q.1, q.2 i)) p :=
    analyticAt_fst.prod (coordinate_analyticAt p i)
  have hS (i : Fin N) : AnalyticAt ℂ
      (fun q : RegularJointSpace N => jointParameterDerivative explicitRightInverse (q.1, q.2 i)) p :=
    (jointParameterDerivative_analyticAt _ _ (hU i)).comp
      (f := fun q : RegularJointSpace N => (q.1, q.2 i)) (hm i)
  have hv : AnalyticAt ℂ
      (fun q : RegularJointSpace N => jointCoordinateDerivative explicitRightInverse (q.1, q.2 a)) p :=
    (jointCoordinateDerivative_analyticAt _ _ (hU a)).comp
      (f := fun q : RegularJointSpace N => (q.1, q.2 a)) (hm a)
  apply AnalyticAt.pi
  intro i
  by_cases hi : i = a
  · subst i
    simp only [anchoredRegularField, ite_true]
    convert ((Finset.analyticAt_fun_sum _ (fun j _ => hS j)).neg.div hv ha) using 1
  · simpa only [anchoredRegularField, ite_eq_right hi] using
      (analyticAt_const (𝕜 := ℂ) (x := p) (v := (0 : ℂ)))

theorem anchoredCutoffCoefficient_analyticAt {N : ℕ} (a : Fin N) (p : RegularJointSpace N)
    (hU : ∀ i, AnalyticAt ℂ explicitRightInverse (p.1, p.2 i))
    (ha : jointCoordinateDerivative explicitRightInverse (p.1, p.2 a) ≠ 0) (i : Fin N) :
    AnalyticAt ℂ (fun q => anchoredCutoffCoefficient a q i) p := by
  have hm : AnalyticAt ℂ (fun q : RegularJointSpace N => (q.1, q.2 i)) p :=
    analyticAt_fst.prod (coordinate_analyticAt p i)
  have hS := (jointParameterDerivative_analyticAt _ _ (hU i)).comp
    (f := fun q : RegularJointSpace N => (q.1, q.2 i)) hm
  have hv := (jointCoordinateDerivative_analyticAt _ _ (hU i)).comp
    (f := fun q : RegularJointSpace N => (q.1, q.2 i)) hm
  have hB : AnalyticAt ℂ (fun q => anchoredRegularField a q i) p :=
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) i).analyticAt _).comp
      (anchoredRegularField_analyticAt a p hU ha)
  exact hS.add (hv.mul hB)

theorem anchoredRegularField_norm_bound {N : ℕ} (a : Fin N) (p : RegularJointSpace N)
    (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c)
    (hS : ∀ i, ‖jointParameterDerivative explicitRightInverse (p.1, p.2 i)‖ ≤ C)
    (ha : c ≤ ‖jointCoordinateDerivative explicitRightInverse (p.1, p.2 a)‖) :
    ‖anchoredRegularField a p‖ ≤ (N : ℝ) * C / c := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  by_cases hi : i = a
  · subst i
    simp only [anchoredRegularField, ite_true, norm_div, norm_neg]
    apply div_le_div₀ (by positivity) ?_ hc ha
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun j _ => hS j)).trans_eq (by simp))
  · simp only [anchoredRegularField, ite_eq_right hi, norm_zero]
    positivity

theorem anchoredCutoffCoefficient_norm_bound {N : ℕ} (a : Fin N) (p : RegularJointSpace N)
    (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c)
    (hS : ∀ i, ‖jointParameterDerivative explicitRightInverse (p.1, p.2 i)‖ ≤ C)
    (hv : ∀ i, ‖jointCoordinateDerivative explicitRightInverse (p.1, p.2 i)‖ ≤ C)
    (ha : c ≤ ‖jointCoordinateDerivative explicitRightInverse (p.1, p.2 a)‖) (i : Fin N) :
    ‖anchoredCutoffCoefficient a p i‖ ≤ C * (1 + (N : ℝ) * C / c) := by
  have hB := anchoredRegularField_norm_bound a p C c hC hc hS ha
  calc
    _ ≤ ‖jointParameterDerivative explicitRightInverse (p.1, p.2 i)‖ +
        ‖jointCoordinateDerivative explicitRightInverse (p.1, p.2 i)‖ *
          ‖anchoredRegularField a p i‖ := by
      simpa only [anchoredCutoffCoefficient, norm_mul] using norm_add_le
        (jointParameterDerivative explicitRightInverse (p.1, p.2 i))
        (jointCoordinateDerivative explicitRightInverse (p.1, p.2 i) * anchoredRegularField a p i)
    _ ≤ C + C * ((N : ℝ) * C / c) :=
      add_le_add (hS i) (mul_le_mul (hv i) ((norm_le_pi_norm _ i).trans hB) (norm_nonneg _) hC)
    _ = _ := by ring

def actualAnchoredRegularField {N : ℕ} (a : Fin N) (η τ ξ : ℝ)
    (i : Fin N) (q : ℂ × (Fin N → ℝ)) : ℂ :=
  anchoredRegularField a (regularJointMap (actualPhysicalCoordinate η τ ξ) q) i

def actualAnchoredAngularVelocity {N : ℕ} (a : Fin N) (η τ ξ : ℝ)
    (i : Fin N) (q : ℂ × (Fin N → ℝ)) : ℂ :=
  constructedAngularVelocity (actualPhysicalCoordinate η τ ξ) actualAngularDirection
    actualTimeDirection (actualAnchoredRegularField a η τ ξ) i q

/-- Generic full balanced inverse identity, valid for the actual anchor field
and any other regular field with the same genuine coordinate derivative. -/
theorem constructedActualVelocity_balanced {N : ℕ} (η τ ξ : ℝ)
    (B : Fin N → (ℂ × (Fin N → ℝ)) → ℂ) (q : ℂ × (Fin N → ℝ))
    (hq : ∀ i, 0 < (isotropicDispersion (q.1, actualHomotopyAngle η τ ξ q.2 i)).im)
    (hdet : actualCoordinateDeterminant η τ ξ q ≠ 0)
    (hdata : ∀ i,
      AnalyticAt ℂ explicitRightInverse (q.1, actualPhysicalCoordinate η τ ξ i q) ∧
      Complex.cos (actualPhysicalCoordinate η τ ξ i q / 2) ≠ 0 ∧
      explicitRightDenominator (q.1, actualPhysicalCoordinate η τ ξ i q) ≠ 0 ∧
      explicitRightInverse (q.1, actualPhysicalCoordinate η τ ξ i q) =
        actualHomotopyAngle η τ ξ q.2 i) :
    actualBalancedJacobian η τ ξ q.2
      (fun i => constructedAngularVelocity (actualPhysicalCoordinate η τ ξ)
        actualAngularDirection actualTimeDirection B i q) =
      fun i => -(jointParameterDerivative explicitRightInverse
          (q.1, actualPhysicalCoordinate η τ ξ i q) +
        jointCoordinateDerivative explicitRightInverse
          (q.1, actualPhysicalCoordinate η τ ξ i q) * B i q) := by
  let χ := actualPhysicalCoordinate (ι := Fin N) η τ ξ
  let e := actualAngularDirection (ι := Fin N)
  let V := fun i => constructedAngularVelocity χ e actualTimeDirection B i q
  have ht := constructedAngularVelocity_transport χ e actualTimeDirection q B hdet
  have hmat := actualPhysicalCoordinate_matrix η τ ξ q hq
  funext i
  obtain ⟨hc, ha⟩ := actual_inverse_chain_coefficients η τ ξ q i (hq i)
    (hdata i).1 (hdata i).2.1 (hdata i).2.2.1 (hdata i).2.2.2
  let u := jointCoordinateDerivative explicitRightInverse (q.1, actualPhysicalCoordinate η τ ξ i q)
  change u * actualCoordinateMultiplier η τ ξ q i = 1 at hc
  have hentry (j : Fin N) : u * scalarCoordinateMatrix χ e q i j = actualBalancedMatrix η τ ξ q.2 i j := by
    rw [hmat, Matrix.diagonal_mul, ← mul_assoc, hc, one_mul]
  have hsum : u * (∑ j, scalarCoordinateMatrix χ e q i j * V j) =
      actualBalancedJacobian η τ ξ q.2 V i := by
    rw [Finset.mul_sum]
    calc
      _ = ∑ j, actualBalancedMatrix η τ ξ q.2 i j * V j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [← mul_assoc, hentry]
      _ = _ := congrFun (LinearMap.toMatrix'_mulVec (actualBalancedJacobian η τ ξ q.2) V) i
  have hti := congrFun ht i
  change scalarPartial (χ i) actualTimeDirection q -
      (∑ j, scalarCoordinateMatrix χ e q i j * V j) = B i q at hti
  change u * scalarPartial (χ i) actualTimeDirection q = _ at ha
  change u * scalarPartial (χ i) actualTimeDirection q =
    -jointParameterDerivative explicitRightInverse (q.1, χ i q) at ha
  change actualBalancedJacobian η τ ξ q.2 V i = _
  rw [← hsum]
  change u * (∑ j, scalarCoordinateMatrix χ e q i j * V j) =
    -(jointParameterDerivative explicitRightInverse (q.1, χ i q) + u * B i q)
  linear_combination -u * hti + ha

theorem actualAnchoredAngularVelocity_tangent {N : ℕ} (a : Fin N) (η τ ξ : ℝ)
    (q : ℂ × (Fin N → ℝ))
    (hq : ∀ i, 0 < (isotropicDispersion (q.1, actualHomotopyAngle η τ ξ q.2 i)).im)
    (hdet : actualCoordinateDeterminant η τ ξ q ≠ 0)
    (hdata : ∀ i,
      AnalyticAt ℂ explicitRightInverse (q.1, actualPhysicalCoordinate η τ ξ i q) ∧
      Complex.cos (actualPhysicalCoordinate η τ ξ i q / 2) ≠ 0 ∧
      explicitRightDenominator (q.1, actualPhysicalCoordinate η τ ξ i q) ≠ 0 ∧
      explicitRightInverse (q.1, actualPhysicalCoordinate η τ ξ i q) =
        actualHomotopyAngle η τ ξ q.2 i)
    (ha : jointCoordinateDerivative explicitRightInverse
      (q.1, actualPhysicalCoordinate η τ ξ a q) ≠ 0) :
    (∑ i, actualAnchoredAngularVelocity a η τ ξ i q) = 0 := by
  have hV := constructedActualVelocity_balanced η τ ξ (actualAnchoredRegularField a η τ ξ) q hq hdet hdata
  have hs : (∑ i, actualAnchoredAngularVelocity a η τ ξ i q) =
      ∑ i, -(jointParameterDerivative explicitRightInverse
        (q.1, actualPhysicalCoordinate η τ ξ i q) +
        jointCoordinateDerivative explicitRightInverse (q.1, actualPhysicalCoordinate η τ ξ i q) *
          actualAnchoredRegularField a η τ ξ i q) := by
    have hh := congrArg (fun v : Fin N → ℂ => ∑ i, v i) hV
    simp only [actualBalancedJacobian, sum_balancedAngularJacobian] at hh
    exact hh
  rw [hs]
  change (∑ i, -anchoredCutoffCoefficient a
    (regularJointMap (actualPhysicalCoordinate η τ ξ) q) i) = 0
  have hsum := anchoredCutoffCoefficient_sum a
    (regularJointMap (actualPhysicalCoordinate η τ ξ) q) ha
  rw [Finset.sum_neg_distrib, hsum, neg_zero]

end IsingBulk.AnisoF002.Isotropic
