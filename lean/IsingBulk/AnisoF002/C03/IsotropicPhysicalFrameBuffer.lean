import IsingBulk.AnisoF002.C03.IsotropicInverseVelocityGerm

/-!
# The actual full transport frame on a geometric angular buffer

The angular interval precedes the smooth bump width. After that width
is fixed, the deformation is chosen small enough for the full inverse
Jacobian. No smallness relation between the bump width and this later
deformation radius is imposed.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators ContDiff
open Set Metric Filter

theorem exists_actual_physical_frame_buffer (S : ℝ) (hS : 0 < S ∧ S < 2) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ ∀ η : ℝ, 0 < η →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ β ∧
      (∀ k : ℕ, ∃ Ck : ℝ, 0 < Ck ∧ ∀ (N : ℕ), 0 < N →
        ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
          ∀ i j : Fin N, FiniteJetControl k (actualBalancedInverseEntry η τ ξ i j)
            (Ck * (N : ℝ) ^ (3 * k))) ∧
      ∀ (N : ℕ), 0 < N → ∀ (s : ℂ), 0 < s.im → dist s (S : ℂ) < δ →
      ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
      ∀ θ : Fin N → ℝ, (∀ i, θ i ∈ Icc (-rightBranchEndpoint S - β) β) →
        (∀ i, ContDiffAt ℝ 2 (actualPhysicalCoordinate η τ ξ i) (s, θ)) ∧
        actualCoordinateDeterminant η τ ξ (s, θ) ≠ 0 ∧
        (∀ i, AnalyticAt ℂ explicitRightInverse (s, actualPhysicalCoordinate η τ ξ i (s, θ))) ∧
        (∀ᶠ y in 𝓝 (s, θ), ∀ i, actualCovarianceAngularVelocity η τ ξ i y =
          -∑ j, actualBalancedInverseEntry η τ ξ i j y.2 *
            rightCutoffTransportCoefficient (regularJointMap (actualPhysicalCoordinate η τ ξ) y) j) := by
  obtain ⟨r, hr, hinverse⟩ := exists_actual_oneSided_inverse_data S hS
  let β := min 1 (r / 2)
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβ1 : β ≤ 1 := min_le_left _ _
  have hβr : β < r := (min_le_right _ _).trans_lt (half_lt_self hr)
  have hb : rightBranchEndpoint S < Real.pi := rightBranchEndpoint_lt_pi S hS.1
  refine ⟨β, hβ, hβ1, ?_⟩
  intro η hη
  obtain ⟨δM, hδM, _, hnear⟩ := exists_actual_balanced_operator_near_one η
  obtain ⟨δE, hδE, _, hjets⟩ := exists_actual_inverse_entries_all_angular_jets η
  let δ := min β (min δM δE)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδβ : δ ≤ β := min_le_left _ _
  have hδM' : δ ≤ δM := (min_le_right _ _).trans (min_le_left _ _)
  have hδE' : δ ≤ δE := (min_le_right _ _).trans (min_le_right _ _)
  have hδr : δ < r := hδβ.trans_lt hβr
  refine ⟨δ, hδ, hδβ, ?_, ?_⟩
  · intro k
    obtain ⟨Ck, hCk, hC⟩ := hjets k
    exact ⟨Ck, hCk, fun N hN τ ξ hτ hξ i j =>
      hC N hN τ ξ ⟨hτ.1, hτ.2.trans hδE'⟩ hξ i j⟩
  · intro N hN s hs hsnear τ ξ hτ hξ θ hθ
    have hτr : τ ∈ Icc 0 r := ⟨hτ.1, hτ.2.trans hδr.le⟩
    have hτM : τ ∈ Icc 0 δM := ⟨hτ.1, hτ.2.trans hδM'⟩
    have hθr : ∀ i, θ i ∈ Icc (-Real.pi - r) r :=
      fun i => ⟨by linarith only [(hθ i).1, hb, hβr], (hθ i).2.trans hβr.le⟩
    have hdata := hinverse N hN s hs (hsnear.trans hδr) η τ ξ hη hτr hξ θ hθr
    have hsheet (i : Fin N) : 0 < (isotropicDispersion (s, actualHomotopyAngle η τ ξ θ i)).im :=
      actual_balanced_homotopy_sheet s hs η τ ξ hη hτ.1 hξ.1 θ i
    have hχ (i : Fin N) : ContDiffAt ℝ 2 (actualPhysicalCoordinate η τ ξ i) (s, θ) :=
      actualPhysicalCoordinate_contDiffAt η τ ξ i (s, θ) 2 (hsheet i)
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
    refine ⟨hχ, hdet, fun i => (hdata i).1, ?_⟩
    have hJ : DifferentiableAt ℝ (actualCoordinateDeterminant η τ ξ) (s, θ) :=
      scalarCoordinateDet_differentiableAt (actualPhysicalCoordinate η τ ξ) actualAngularDirection (s, θ) hχ
    have hsim : ContinuousAt (fun q : ℂ × (Fin N → ℝ) => q.1.im) (s, θ) := by fun_prop
    have hdist : ContinuousAt (fun q : ℂ × (Fin N → ℝ) => dist q.1 (S : ℂ)) (s, θ) := by fun_prop
    have hangle (i : Fin N) : ∀ᶠ q : ℂ × (Fin N → ℝ) in 𝓝 (s, θ),
        q.2 i ∈ Icc (-Real.pi - r) r := by
      have hi : θ i ∈ Ioo (-Real.pi - r) r :=
        ⟨by linarith only [(hθ i).1, hb, hβr], (hθ i).2.trans_lt hβr⟩
      have hc : ContinuousAt (fun q : ℂ × (Fin N → ℝ) => q.2 i) (s, θ) := by fun_prop
      exact (hc.eventually (isOpen_Ioo.mem_nhds hi)).mono (fun _ hx => ⟨hx.1.le, hx.2.le⟩)
    filter_upwards [hsim.eventually (Ioi_mem_nhds hs),
      hdist.eventually (Iio_mem_nhds (hsnear.trans hδr)), Filter.eventually_all.mpr hangle,
      hJ.continuousAt.eventually_ne hdet] with y hys hyd hyθ hyJ
    intro i
    exact actualCovarianceAngularVelocity_inverse_entries η τ ξ y
      (fun j => actual_balanced_homotopy_sheet y.1 hys η τ ξ hη hτ.1 hξ.1 y.2 j) hyJ
      (hinverse N hN y.1 hys hyd η τ ξ hη hτr hξ y.2 hyθ)
      (hnear N hN τ ξ hτM hξ y.2) i

end IsingBulk.AnisoF002.Isotropic
