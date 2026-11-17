import IsingBulk.AnisoF002.C03.IsotropicActualWordExpansion

/-!
# The inverse-velocity word identity on the actual physical neighborhood

The neighborhood identity required by the differentiated word expansion
is obtained from the actual one-sided inverse and full balanced Jacobian.
Its radius is chosen before particle number and before derivative order.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators ContDiff
open Set Metric Filter

theorem exists_actual_inverse_entries_smooth (η : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ (N : ℕ), 0 < N →
      ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
        ∀ i j : Fin N, ContDiff ℝ ∞ (actualBalancedInverseEntry η τ ξ i j) := by
  obtain ⟨δ, hδ, hδ1, hjets⟩ := exists_actual_inverse_entries_all_angular_jets η
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro N hN τ ξ hτ hξ i j
  apply contDiff_infty.mpr
  intro k
  obtain ⟨Ck, _, hCk⟩ := hjets k
  exact (hCk N hN τ ξ hτ hξ i j).smooth

theorem exists_actual_inverse_velocity_germ (S η : ℝ)
    (hS : 0 < S ∧ S < 2) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ (N : ℕ), 0 < N → ∀ (s : ℂ), 0 < s.im → dist s (S : ℂ) < δ →
      ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
      ∀ θ : Fin N → ℝ, (∀ i, θ i ∈ Icc (-rightBranchEndpoint S - δ) δ) →
        (∀ i, AnalyticAt ℂ explicitRightInverse (s, actualPhysicalCoordinate η τ ξ i (s, θ))) ∧
        (actualCoordinateDeterminant η τ ξ (s, θ) ≠ 0 →
          ∀ᶠ y in 𝓝 (s, θ), ∀ i, actualCovarianceAngularVelocity η τ ξ i y =
            -∑ j, actualBalancedInverseEntry η τ ξ i j y.2 *
              rightCutoffTransportCoefficient (regularJointMap (actualPhysicalCoordinate η τ ξ) y) j) := by
  obtain ⟨r, hr, hinverse⟩ := exists_actual_oneSided_inverse_data S hS
  obtain ⟨δM, hδM, hδM1, hnear⟩ := exists_actual_balanced_operator_near_one η
  let δ := min (r / 2) δM
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδr : δ < r := (min_le_left _ _).trans_lt (half_lt_self hr)
  have hδM' : δ ≤ δM := min_le_right _ _
  have hb : rightBranchEndpoint S < Real.pi := rightBranchEndpoint_lt_pi S hS.1
  refine ⟨δ, hδ, hδM'.trans hδM1, ?_⟩
  intro N hN s hs hsnear τ ξ hτ hξ θ hθ
  have hτr : τ ∈ Icc 0 r := ⟨hτ.1, hτ.2.trans hδr.le⟩
  have hτM : τ ∈ Icc 0 δM := ⟨hτ.1, hτ.2.trans hδM'⟩
  have hθr : ∀ i, θ i ∈ Icc (-Real.pi - r) r :=
    fun i => ⟨by linarith only [(hθ i).1, hb, hδr], (hθ i).2.trans hδr.le⟩
  have hdata := hinverse N hN s hs (hsnear.trans hδr) η τ ξ hη hτr hξ θ hθr
  refine ⟨fun i => (hdata i).1, ?_⟩
  intro hdet
  have hχ (i : Fin N) : ContDiffAt ℝ 2 (actualPhysicalCoordinate η τ ξ i) (s, θ) :=
    actualPhysicalCoordinate_contDiffAt η τ ξ i (s, θ) 2
      (actual_balanced_homotopy_sheet s hs η τ ξ hη hτ.1 hξ.1 θ i)
  have hJ : DifferentiableAt ℝ (actualCoordinateDeterminant η τ ξ) (s, θ) :=
    scalarCoordinateDet_differentiableAt (actualPhysicalCoordinate η τ ξ) actualAngularDirection (s, θ) hχ
  have hsim : ContinuousAt (fun q : ℂ × (Fin N → ℝ) => q.1.im) (s, θ) := by fun_prop
  have hdist : ContinuousAt (fun q : ℂ × (Fin N → ℝ) => dist q.1 (S : ℂ)) (s, θ) := by fun_prop
  have hangle (i : Fin N) : ∀ᶠ q : ℂ × (Fin N → ℝ) in 𝓝 (s, θ),
      q.2 i ∈ Icc (-Real.pi - r) r := by
    have hi : θ i ∈ Ioo (-Real.pi - r) r :=
      ⟨by linarith only [(hθ i).1, hb, hδr], (hθ i).2.trans_lt hδr⟩
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
