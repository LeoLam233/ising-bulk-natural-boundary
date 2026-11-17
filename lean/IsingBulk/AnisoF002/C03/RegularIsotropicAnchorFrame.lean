import IsingBulk.AnisoF002.C03.RegularIsotropicAnchorField
import IsingBulk.AnisoF002.C03.RegularIsotropicCoordinateGerms
import IsingBulk.AnisoF002.C03.IsotropicPhysicalFrameBuffer

/-!
# Actual anchored field and complete smooth frame on the whole one-sided arc

The independent angular buffer is fixed before the bump width. The later
deformation radius is chosen before N and before derivative order. No
variance denominator or separation from total coincidence is needed.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators ContDiff
open Set Filter Metric

theorem actualAnchoredAngularVelocity_inverse_entries {N : ℕ} (a : Fin N) (η τ ξ : ℝ)
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
    actualAnchoredAngularVelocity a η τ ξ i q =
      -∑ j, actualBalancedInverseEntry η τ ξ i j q.2 *
        anchoredCutoffCoefficient a (regularJointMap (actualPhysicalCoordinate η τ ξ) q) j := by
  let V : Fin N → ℂ := fun j => actualAnchoredAngularVelocity a η τ ξ j q
  let K : Fin N → ℂ := fun j =>
    anchoredCutoffCoefficient a (regularJointMap (actualPhysicalCoordinate η τ ξ) q) j
  have ht : actualBalancedOperator η τ ξ q.2 V = -K :=
    constructedActualVelocity_balanced η τ ξ (actualAnchoredRegularField a η τ ξ) q hq hdet hdata
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

theorem actual_inverse_coordinate_slope_ne_zero {N : ℕ} (η τ ξ : ℝ)
    (q : ℂ × (Fin N → ℝ)) (i : Fin N)
    (hq : 0 < (isotropicDispersion (q.1, actualHomotopyAngle η τ ξ q.2 i)).im)
    (hdata : AnalyticAt ℂ explicitRightInverse (q.1, actualPhysicalCoordinate η τ ξ i q) ∧
      Complex.cos (actualPhysicalCoordinate η τ ξ i q / 2) ≠ 0 ∧
      explicitRightDenominator (q.1, actualPhysicalCoordinate η τ ξ i q) ≠ 0 ∧
      explicitRightInverse (q.1, actualPhysicalCoordinate η τ ξ i q) =
        actualHomotopyAngle η τ ξ q.2 i) :
    jointCoordinateDerivative explicitRightInverse (q.1, actualPhysicalCoordinate η τ ξ i q) ≠ 0 := by
  have hh := (actual_inverse_chain_coefficients η τ ξ q i hq
    hdata.1 hdata.2.1 hdata.2.2.1 hdata.2.2.2).1
  intro hz
  change jointCoordinateDerivative explicitRightInverse (q.1, actualPhysicalCoordinate η τ ξ i q) *
    actualCoordinateMultiplier η τ ξ q i = 1 at hh
  rw [hz, zero_mul] at hh
  exact zero_ne_one hh

theorem exists_actual_anchored_frame_buffer (S : ℝ) (hS : 0 < S ∧ S < 2) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ ∀ η : ℝ, 0 < η →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ β ∧
      (∀ k : ℕ, ∃ Ck : ℝ, 0 < Ck ∧ ∀ N : ℕ, 0 < N →
        ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 → ∀ i j : Fin N,
          FiniteJetControl k (actualBalancedInverseEntry η τ ξ i j) (Ck * (N : ℝ) ^ (3 * k))) ∧
      ∀ N : ℕ, 0 < N → ∀ s : ℂ, 0 < s.im → dist s (S : ℂ) < δ →
      ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 → ∀ θ : Fin N → ℝ,
      (∀ i, θ i ∈ Icc (-Real.pi - β) β) → ∀ a : Fin N,
        (∀ i, ContDiffAt ℝ ∞ (actualPhysicalCoordinate η τ ξ i) (s, θ)) ∧
        actualCoordinateDeterminant η τ ξ (s, θ) ≠ 0 ∧
        (∀ i, AnalyticAt ℂ explicitRightInverse (s, actualPhysicalCoordinate η τ ξ i (s, θ))) ∧
        AnalyticAt ℂ (anchoredRegularField a) (regularJointMap (actualPhysicalCoordinate η τ ξ) (s, θ)) ∧
        (∀ i, AnalyticAt ℂ (fun p => anchoredCutoffCoefficient a p i)
          (regularJointMap (actualPhysicalCoordinate η τ ξ) (s, θ))) ∧
        (∀ᶠ y in 𝓝 (s, θ), (∑ i, actualAnchoredAngularVelocity a η τ ξ i y) = 0 ∧
          ∀ i, actualAnchoredAngularVelocity a η τ ξ i y =
            -∑ j, actualBalancedInverseEntry η τ ξ i j y.2 *
              anchoredCutoffCoefficient a (regularJointMap (actualPhysicalCoordinate η τ ξ) y) j) := by
  obtain ⟨r, hr, hinverse⟩ := exists_actual_oneSided_inverse_data S hS
  let β := min 1 (r / 2)
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβ1 : β ≤ 1 := min_le_left _ _
  have hβr : β < r := (min_le_right _ _).trans_lt (half_lt_self hr)
  refine ⟨β, hβ, hβ1, ?_⟩
  intro η hη
  obtain ⟨δM, hδM, _, hnear⟩ := exists_actual_balanced_operator_near_one η
  obtain ⟨δE, hδE, _, hjets⟩ := exists_actual_inverse_entries_all_angular_jets η
  let δ := min β (min δM δE)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hdβ : δ ≤ β := min_le_left _ _
  have hdM : δ ≤ δM := (min_le_right _ _).trans (min_le_left _ _)
  have hdE : δ ≤ δE := (min_le_right _ _).trans (min_le_right _ _)
  have hdr : δ < r := hdβ.trans_lt hβr
  refine ⟨δ, hδ, hdβ, ?_, ?_⟩
  · intro k
    obtain ⟨Ck, hCk, hk⟩ := hjets k
    exact ⟨Ck, hCk, fun N hN τ ξ hτ hξ i j => hk N hN τ ξ ⟨hτ.1, hτ.2.trans hdE⟩ hξ i j⟩
  · intro N hN s hs hsnear τ ξ hτ hξ θ hθ a
    have hτr : τ ∈ Icc 0 r := ⟨hτ.1, hτ.2.trans hdr.le⟩
    have hτM : τ ∈ Icc 0 δM := ⟨hτ.1, hτ.2.trans hdM⟩
    have hθr : ∀ i, θ i ∈ Icc (-Real.pi - r) r :=
      fun i => ⟨by linarith only [(hθ i).1, hβr], (hθ i).2.trans hβr.le⟩
    have hdata := hinverse N hN s hs (hsnear.trans hdr) η τ ξ hη hτr hξ θ hθr
    have hsheet (i : Fin N) : 0 < (isotropicDispersion (s, actualHomotopyAngle η τ ξ θ i)).im :=
      actual_balanced_homotopy_sheet s hs η τ ξ hη hτ.1 hξ.1 θ i
    have hχ (i : Fin N) : ContDiffAt ℝ ∞ (actualPhysicalCoordinate η τ ξ i) (s, θ) :=
      actualPhysicalCoordinate_contDiffAt η τ ξ i (s, θ) ⊤ (hsheet i)
    have hD (i : Fin N) : Complex.sin (actualPhysicalPhase η τ ξ (s, θ) i) -
        Complex.sin (actualHomotopyAngle η τ ξ θ i) ≠ 0 := by
      have hd := (hdata i).2.2.1
      unfold explicitRightDenominator at hd
      rw [(hdata i).2.2.2] at hd
      simpa only [actualPhysicalCoordinate, physicalRegularCoordinate, add_sub_cancel_left,
        actualPhysicalPhase] using hd
    have hM : Function.Injective (actualBalancedJacobian η τ ξ θ) := by
      have hi := (actualBalancedOperator_inverse_identity η τ ξ θ (hnear N hN τ ξ hτM hξ θ)).2
      have hleft : Function.LeftInverse (actualBalancedInverseOperator η τ ξ θ)
          (actualBalancedJacobian η τ ξ θ) := by
        intro v
        change (actualBalancedInverseOperator η τ ξ θ * actualBalancedOperator η τ ξ θ) v = v
        rw [hi]
        rfl
      exact hleft.injective
    have hdet := actualCoordinateDeterminant_ne_zero η τ ξ (s, θ) hsheet hM hD
    have ha := actual_inverse_coordinate_slope_ne_zero η τ ξ (s, θ) a (hsheet a) (hdata a)
    let p : RegularJointSpace N := regularJointMap (actualPhysicalCoordinate η τ ξ) (s, θ)
    have hUp (i : Fin N) : AnalyticAt ℂ explicitRightInverse (p.1, p.2 i) := (hdata i).1
    have hap : jointCoordinateDerivative explicitRightInverse (p.1, p.2 a) ≠ 0 := ha
    refine ⟨hχ, hdet, fun i => (hdata i).1,
      anchoredRegularField_analyticAt a p hUp hap,
      fun i => anchoredCutoffCoefficient_analyticAt a p hUp hap i, ?_⟩
    have hχ2 (i : Fin N) : ContDiffAt ℝ 2 (actualPhysicalCoordinate η τ ξ i) (s, θ) :=
      (hχ i).of_le (by simp)
    have hJ := scalarCoordinateDet_differentiableAt (actualPhysicalCoordinate η τ ξ)
      actualAngularDirection (s, θ) hχ2
    have hsim : ContinuousAt (fun q : ℂ × (Fin N → ℝ) => q.1.im) (s, θ) := by fun_prop
    have hdist : ContinuousAt (fun q : ℂ × (Fin N → ℝ) => dist q.1 (S : ℂ)) (s, θ) := by fun_prop
    have hangle (i : Fin N) : ∀ᶠ q : ℂ × (Fin N → ℝ) in 𝓝 (s, θ),
        q.2 i ∈ Icc (-Real.pi - r) r := by
      have hi : θ i ∈ Ioo (-Real.pi - r) r :=
        ⟨by linarith only [(hθ i).1, hβr], (hθ i).2.trans_lt hβr⟩
      have hc : ContinuousAt (fun q : ℂ × (Fin N → ℝ) => q.2 i) (s, θ) := by fun_prop
      exact (hc.eventually (isOpen_Ioo.mem_nhds hi)).mono (fun _ hx => ⟨hx.1.le, hx.2.le⟩)
    filter_upwards [hsim.eventually (Ioi_mem_nhds hs),
      hdist.eventually (Iio_mem_nhds (hsnear.trans hdr)), Filter.eventually_all.mpr hangle,
      hJ.continuousAt.eventually_ne hdet] with y hys hyd hyθ hyJ
    have hyW (i : Fin N) := actual_balanced_homotopy_sheet y.1 hys η τ ξ hη hτ.1 hξ.1 y.2 i
    have hydata := hinverse N hN y.1 hys hyd η τ ξ hη hτr hξ y.2 hyθ
    exact ⟨actualAnchoredAngularVelocity_tangent a η τ ξ y hyW hyJ hydata
        (actual_inverse_coordinate_slope_ne_zero η τ ξ y a (hyW a) (hydata a)),
      fun i => actualAnchoredAngularVelocity_inverse_entries a η τ ξ y hyW hyJ hydata
        (hnear N hN τ ξ hτM hξ y.2) i⟩

end IsingBulk.AnisoF002.Isotropic
