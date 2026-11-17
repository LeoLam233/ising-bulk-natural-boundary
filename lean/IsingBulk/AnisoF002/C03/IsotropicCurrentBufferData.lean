import IsingBulk.AnisoF002.C03.IsotropicActualCovariance
import IsingBulk.AnisoF002.C03.IsotropicPhysicalFrameBuffer
import IsingBulk.AnisoF002.C03.IsotropicIteratedCurrent

/-!
# Actual covariance and smooth current on an independent angular buffer

The compact angular geometry is selected before the smooth bump width.
Only the small complex-parameter and deformation radius depends on that
width. The variance, field analyticity, inverse-Jacobian velocity, and
its exact tangency are proved for the complete actual homotopy.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators ContDiff
open Set Metric Filter

theorem exists_actual_right_covariance_transport_buffer (S : ℝ)
    (hS : 0 < S ∧ S < 2) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ ∀ η : ℝ, 0 < η →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ β ∧
      ∀ (N : ℕ), 0 < N → ∀ (s : ℂ), 0 < s.im → dist s (S : ℂ) < δ →
      ∀ τ ∈ Icc 0 δ, ∀ ξ ∈ Icc 0 1, ∀ θ : Fin N → ℝ,
        (∀ k, θ k ∈ Icc (-rightBranchEndpoint S - β) β) →
        ∀ i j, θ i ≠ θ j →
        let v := (actualHomotopyRegularTuple s η τ ξ θ).2
        AnalyticAt ℂ (fun p : ℂ × (Fin N → ℂ) => rightCovarianceField p.1 p.2) (s, v) ∧
          (∑ k, rightCovarianceField s v k) = 0 ∧
          (∑ k, deriv (fun z => explicitRightInverse (s, z)) (v k) *
            rightCovarianceField s v k) = rightCovarianceAmplitude s v ∧
          HasDerivAt (fun t : ℂ => ∑ k,
            ((v k + t * rightCovarianceField s v k) -
              explicitRightInverse (s + t, v k + t * rightCovarianceField s v k))) 0 0 ∧
          ∃ V : Fin N → ℂ,
            actualBalancedJacobian η τ ξ θ V = (fun k =>
              -(deriv (fun z => explicitRightInverse (z, v k)) s +
                deriv (fun z => explicitRightInverse (s, z)) (v k) * rightCovarianceField s v k)) ∧
            (∑ k, V k) = 0 ∧
            ‖V‖ ≤ 2 * ‖fun k =>
              -(deriv (fun z => explicitRightInverse (z, v k)) s +
                deriv (fun z => explicitRightInverse (s, z)) (v k) * rightCovarianceField s v k)‖ := by
  obtain ⟨r₁, _, hr₁, _, _, _, _, hfield⟩ := exists_rightCovariance_common_domain S hS
  obtain ⟨r₂, c₂, hr₂, hc₂, _, hfirst, hsecond, _, hlower, _⟩ :=
    exists_right_secants_protected_neighborhood S hS
  obtain ⟨r₃, _, hr₃, _, _, _, hU, _, _⟩ :=
    exists_right_inverse_common_convex_neighborhood S hS
  let r := min r₁ (min r₂ r₃)
  have hr : 0 < r := lt_min hr₁ (lt_min hr₂ hr₃)
  have hr1 : r ≤ r₁ := min_le_left _ _
  have hr2 : r ≤ r₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hr3 : r ≤ r₃ := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨δ₁, hδ₁, himage⟩ := exists_actual_right_homotopy_domain S r hS hr
  let β := min 1 δ₁
  have hβ : 0 < β := lt_min zero_lt_one hδ₁
  have hβ1 : β ≤ 1 := min_le_left _ _
  have hβd : β ≤ δ₁ := min_le_right _ _
  refine ⟨β, hβ, hβ1, ?_⟩
  intro η hη
  obtain ⟨δ₂, _, hδ₂, _, hregular⟩ := exists_actual_balanced_uniform_regularity η
  let δ := min β δ₂
  have hδ : 0 < δ := lt_min hβ hδ₂
  have hdβ : δ ≤ β := min_le_left _ _
  have hd1 : δ ≤ δ₁ := hdβ.trans hβd
  have hd2 : δ ≤ δ₂ := min_le_right _ _
  refine ⟨δ, hδ, hdβ, ?_⟩
  intro N hN s hs hsnear τ hτ ξ hξ θ hθ i j hij
  let q := actualHomotopyRegularTuple s η τ ξ θ
  let v := q.2
  have ht1 : τ ∈ Icc 0 δ₁ := ⟨hτ.1, hτ.2.trans hd1⟩
  have ht2 : τ ∈ Icc 0 δ₂ := ⟨hτ.1, hτ.2.trans hd2⟩
  have hθ1 : ∀ k, θ k ∈ Icc (-rightBranchEndpoint S - δ₁) δ₁ := by
    intro k
    exact ⟨by linarith [(hθ k).1], (hθ k).2.trans hβd⟩
  obtain ⟨hq, heq⟩ := himage N hN s hs (hsnear.trans_le hd1) η τ ξ hη ht1 hξ θ hθ1
  obtain ⟨hbij, hinv, hvar⟩ := hregular N hN τ ht2 ξ hξ θ
  have hv : pairVariance (fun k => explicitRightInverse (s, v k)) ≠ 0 := by
    have he : (fun k => explicitRightInverse (s, v k)) = actualHomotopyAngle η τ ξ θ :=
      funext heq
    rw [he]
    exact hvar i j hij
  have hsingle : ∀ k, (s, v k) ∈ thickening r (rightParameterSegment S) :=
    fun k => rightSingle_of_thickening hq.1 (hq.2 k)
  have hpair : ∀ k l, (s, v k, v l) ∈ cthickening r₂ (rightPairParameterSegment S) := by
    intro k l
    exact thickening_subset_cthickening r₂ _
      (thickening_mono hr2 _ (rightPair_of_thickening hq.1 (hq.2 k) (hq.2 l)))
  have ha : AnalyticAt ℂ (fun p : ℂ × (Fin N → ℂ) => rightCovarianceField p.1 p.2) (s, v) := by
    apply rightCovarianceField_analyticAt
    · intro k
      exact hU _ (thickening_subset_cthickening r₃ _ (thickening_mono hr3 _ (hsingle k)))
    · intro k l
      exact hfirst _ (hpair k l)
    · intro k l
      exact hsecond _ (hpair k l)
    · intro k l hz
      have hb := hlower _ (hpair k l)
      rw [hz, Complex.zero_re] at hb
      linarith
    · exact hv
  obtain ⟨hsum, hweighted, hphase⟩ := hfield N s v
    (fun k => thickening_mono hr1 _ (hsingle k)) hv
  obtain ⟨V, hV⟩ := hbij.2 (fun k =>
    -(deriv (fun z => explicitRightInverse (z, v k)) s +
      deriv (fun z => explicitRightInverse (s, z)) (v k) * rightCovarianceField s v k))
  refine ⟨ha, hsum, hweighted, hphase, V, hV, ?_, hinv _ _ hV⟩
  exact rightCovarianceField_angular_tangent s v hweighted _
    (fun k => upperPeriodicBump η (θ k)) (fun k => lowerPeriodicBump η (θ k))
    (fun k => deriv (upperPeriodicBump η) (θ k))
    (fun k => deriv (lowerPeriodicBump η) (θ k)) V hV


/-- The genuine full smooth frame and tangent physical velocity on one
angular buffer chosen before the bump width, and one later small radius
chosen before the particle number and differentiation order. -/
theorem exists_actual_right_smooth_current_buffer (S : ℝ)
    (hS : 0 < S ∧ S < 2) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ ∀ η : ℝ, 0 < η →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ β ∧
      ∀ (N : ℕ), 0 < N → ∀ (s : ℂ), 0 < s.im → dist s (S : ℂ) < δ →
      ∀ τ ∈ Icc 0 δ, ∀ ξ ∈ Icc 0 1, ∀ θ : Fin N → ℝ,
        (∀ k, θ k ∈ Icc (-rightBranchEndpoint S - β) β) →
        ∀ i j, θ i ≠ θ j →
        (∀ k, ContDiffAt ℝ ∞ (actualPhysicalCoordinate η τ ξ k) (s, θ)) ∧
        actualCoordinateDeterminant η τ ξ (s, θ) ≠ 0 ∧
        (∀ k, ContDiffAt ℝ ∞ (actualCovarianceRegularField η τ ξ k) (s, θ)) ∧
        (∀ k, DifferentiableAt ℝ (actualCovarianceAngularVelocity η τ ξ k) (s, θ)) ∧
        (∑ k, actualCovarianceAngularVelocity η τ ξ k (s, θ)) = 0 := by
  obtain ⟨β₁, hβ₁, hβ₁1, hframe⟩ := exists_actual_physical_frame_buffer S hS
  obtain ⟨β₂, hβ₂, _, hcov⟩ := exists_actual_right_covariance_transport_buffer S hS
  obtain ⟨r₃, hr₃, hinverse⟩ := exists_actual_oneSided_inverse_data S hS
  let β := min β₁ (min β₂ r₃)
  have hβ : 0 < β := lt_min hβ₁ (lt_min hβ₂ hr₃)
  have hb1 : β ≤ β₁ := min_le_left _ _
  have hb2 : β ≤ β₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hb3 : β ≤ r₃ := (min_le_right _ _).trans (min_le_right _ _)
  have hb := (rightBranchEndpoint_lt_pi S hS.1).le
  refine ⟨β, hβ, hb1.trans hβ₁1, ?_⟩
  intro η hη
  obtain ⟨δ₁, hδ₁, _, _, hdensity⟩ := hframe η hη
  obtain ⟨δ₂, hδ₂, _, hcovariance⟩ := hcov η hη
  let δ := min β (min δ₁ δ₂)
  have hδ : 0 < δ := lt_min hβ (lt_min hδ₁ hδ₂)
  have hdβ : δ ≤ β := min_le_left _ _
  have hd1 : δ ≤ δ₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hd2 : δ ≤ δ₂ := (min_le_right _ _).trans (min_le_right _ _)
  have hd3 : δ ≤ r₃ := hdβ.trans hb3
  refine ⟨δ, hδ, hdβ, ?_⟩
  intro N hN s hs hsnear τ hτ ξ hξ θ hθ i j hij
  have hθ1 : ∀ k, θ k ∈ Icc (-rightBranchEndpoint S - β₁) β₁ :=
    fun k => ⟨by linarith [(hθ k).1], (hθ k).2.trans hb1⟩
  have hθ2 : ∀ k, θ k ∈ Icc (-rightBranchEndpoint S - β₂) β₂ :=
    fun k => ⟨by linarith [(hθ k).1], (hθ k).2.trans hb2⟩
  have hθ3 : ∀ k, θ k ∈ Icc (-Real.pi - r₃) r₃ :=
    fun k => ⟨by linarith [(hθ k).1], (hθ k).2.trans hb3⟩
  obtain ⟨hχ₂, hdet, _, _⟩ := hdensity N hN s hs (hsnear.trans_le hd1) τ ξ
    ⟨hτ.1, hτ.2.trans hd1⟩ hξ θ hθ1
  obtain ⟨hB, _, hw, _, _⟩ := hcovariance N hN s hs (hsnear.trans_le hd2) τ
    ⟨hτ.1, hτ.2.trans hd2⟩ ξ hξ θ hθ2 i j hij
  have hdata := hinverse N hN s hs (hsnear.trans_le hd3) η τ ξ hη
    ⟨hτ.1, hτ.2.trans hd3⟩ hξ θ hθ3
  have hsheet (k : Fin N) : 0 < (isotropicDispersion (s, actualHomotopyAngle η τ ξ θ k)).im :=
    actual_balanced_homotopy_sheet s hs η τ ξ hη hτ.1 hξ.1 θ k
  have hχ (k : Fin N) : ContDiffAt ℝ ∞ (actualPhysicalCoordinate η τ ξ k) (s, θ) :=
    actualPhysicalCoordinate_contDiffAt η τ ξ k (s, θ) ⊤ (hsheet k)
  have hBsmooth := actualCovarianceRegularField_contDiffAt η τ ξ (s, θ) hχ hB
  have hBd := actualCovarianceRegularField_differentiableAt η τ ξ (s, θ) hχ₂ hB
  have hVd := constructedAngularVelocity_differentiableAt
    (actualPhysicalCoordinate η τ ξ) actualAngularDirection actualTimeDirection (s, θ)
    (actualCovarianceRegularField η τ ξ) hχ₂ hBd hdet
  have hV := actualCovarianceAngularVelocity_balanced η τ ξ (s, θ) hsheet hdet hdata
  refine ⟨hχ, hdet, hBsmooth, hVd, ?_⟩
  exact rightCovarianceField_angular_tangent s
    (fun k => actualPhysicalCoordinate η τ ξ k (s, θ)) hw _
    (fun k => upperPeriodicBump η (θ k)) (fun k => lowerPeriodicBump η (θ k))
    (fun k => deriv (upperPeriodicBump η) (θ k))
    (fun k => deriv (lowerPeriodicBump η) (θ k))
    (fun k => actualCovarianceAngularVelocity η τ ξ k (s, θ)) hV

end IsingBulk.AnisoF002.Isotropic
