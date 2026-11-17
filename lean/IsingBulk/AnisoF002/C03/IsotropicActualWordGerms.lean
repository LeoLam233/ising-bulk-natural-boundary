import IsingBulk.AnisoF002.C03.IsotropicActualWordExpansion

/-!
# Neighborhood equality for the actual separated transport expansion

This form permits real differentiation of the complete word sum.  The
equality is established on an actual neighborhood before derivatives
are compared.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Filter
open scoped Topology BigOperators ContDiff

theorem actualTransportDescendant_germ_eq_separated_words {N : ℕ} (η τ ξ : ℝ)
    (F : RegularJointSpace N → ℂ) (g : (Fin N → ℝ) → ℂ)
    (hA : ∀ i j : Fin N, ContDiff ℝ ∞ (actualBalancedInverseEntry η τ ξ i j))
    (hg : ContDiff ℝ ∞ g) (x : ℂ × (Fin N → ℝ))
    (hχ : ∀ i, ContDiffAt ℝ 2 (actualPhysicalCoordinate η τ ξ i) x)
    (hB : AnalyticAt ℂ (fun p : RegularJointSpace N => rightCovarianceField p.1 p.2)
      (regularJointMap (actualPhysicalCoordinate η τ ξ) x))
    (hK : ∀ j, AnalyticAt ℂ (fun p : RegularJointSpace N => rightCutoffTransportCoefficient p j)
      (regularJointMap (actualPhysicalCoordinate η τ ξ) x))
    (hF : AnalyticAt ℂ F (regularJointMap (actualPhysicalCoordinate η τ ξ) x))
    (hdet : actualCoordinateDeterminant η τ ξ x ≠ 0)
    (hV : ∀ᶠ y in 𝓝 x, ∀ i, actualCovarianceAngularVelocity η τ ξ i y =
      -∑ j, actualBalancedInverseEntry η τ ξ i j y.2 *
        rightCutoffTransportCoefficient (regularJointMap (actualPhysicalCoordinate η τ ξ) y) j)
    (n : ℕ) :
    actualTransportDescendant η τ ξ
      (fun y => F (regularJointMap (actualPhysicalCoordinate η τ ξ) y) * g y.2) n =ᶠ[𝓝 x]
      actualSeparatedWordSum η τ ξ F g n := by
  have hm : ContinuousAt (regularJointMap (actualPhysicalCoordinate η τ ξ)) x :=
    continuousAt_fst.prodMk (continuousAt_pi.mpr (fun i => (hχ i).continuousAt))
  have hχnear : ∀ᶠ y in 𝓝 x, ∀ i, ContDiffAt ℝ 2 (actualPhysicalCoordinate η τ ξ i) y :=
    Filter.eventually_all.mpr (fun i => (hχ i).eventually (by norm_num))
  have hdnear : ∀ᶠ y in 𝓝 x, actualCoordinateDeterminant η τ ξ y ≠ 0 :=
    (scalarCoordinateDet_differentiableAt (actualPhysicalCoordinate η τ ξ)
      actualAngularDirection x hχ).continuousAt.eventually_ne hdet
  have hBnear := hm.eventually hB.eventually_analyticAt
  have hKnear : ∀ᶠ y in 𝓝 x, ∀ j, AnalyticAt ℂ
      (fun p : RegularJointSpace N => rightCutoffTransportCoefficient p j)
      (regularJointMap (actualPhysicalCoordinate η τ ξ) y) :=
    Filter.eventually_all.mpr (fun j => hm.eventually (hK j).eventually_analyticAt)
  have hFnear := hm.eventually hF.eventually_analyticAt
  have hVnear := eventually_eventually_nhds.mpr hV
  filter_upwards [hχnear, hdnear, hBnear, hKnear, hFnear, hVnear] with y hχy hdy hBy hKy hFy hVy
  exact actualTransportDescendant_eq_separated_words η τ ξ F g hA hg y
    hχy hBy hKy hFy hdy hVy n

end
end IsingBulk.AnisoF002.Isotropic
