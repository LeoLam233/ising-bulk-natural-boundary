import IsingBulk.AnisoF002.C03.IsotropicActualJacobian
import IsingBulk.AnisoF002.C03.IsotropicAnalyticCovariance

/-!
# Covariance transport on the actual balanced right images

The variance condition in the earlier complex-domain theorem is proved
here for every nonconstant actual angular tuple, allowing every proper
partial diagonal and every population fraction. The actual full Jacobian
then supplies a tangent angular velocity. All neighborhood and deformation
choices precede the particle number.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric

/-- The actual right homotopy supports analytic covariance transport and
an actual tangent angular velocity, without a supplied complex variance
hypothesis or a supplied Jacobian inverse. -/
theorem exists_actual_right_covariance_transport (S η : ℝ)
    (hS : 0 < S ∧ S < 2) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (N : ℕ), 0 < N → ∀ (s : ℂ), 0 < s.im → dist s (S : ℂ) < δ →
      ∀ τ ∈ Icc 0 δ, ∀ ξ ∈ Icc 0 1, ∀ θ : Fin N → ℝ,
        (∀ k, θ k ∈ Icc (-rightBranchEndpoint S - δ) δ) →
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
  obtain ⟨δ₂, _, hδ₂, _, hregular⟩ := exists_actual_balanced_uniform_regularity η
  let δ := min δ₁ δ₂
  have hδ : 0 < δ := lt_min hδ₁ hδ₂
  have hd1 : δ ≤ δ₁ := min_le_left _ _
  have hd2 : δ ≤ δ₂ := min_le_right _ _
  refine ⟨δ, hδ, ?_⟩
  intro N hN s hs hsnear τ hτ ξ hξ θ hθ i j hij
  let q := actualHomotopyRegularTuple s η τ ξ θ
  let v := q.2
  have ht1 : τ ∈ Icc 0 δ₁ := ⟨hτ.1, hτ.2.trans hd1⟩
  have ht2 : τ ∈ Icc 0 δ₂ := ⟨hτ.1, hτ.2.trans hd2⟩
  have hθ1 : ∀ k, θ k ∈ Icc (-rightBranchEndpoint S - δ₁) δ₁ := by
    intro k
    exact ⟨by linarith [(hθ k).1], (hθ k).2.trans hd1⟩
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

end IsingBulk.AnisoF002.Isotropic
