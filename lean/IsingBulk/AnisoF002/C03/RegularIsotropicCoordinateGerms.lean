import IsingBulk.AnisoF002.C03.RegularIsotropicCoordinateWords
import IsingBulk.AnisoF002.C03.IsotropicParameterHolomorphy

/-!
# Genuine germ and parameter holomorphy for general coordinate transport

Every equality is established on a neighborhood before the next real
or complex derivative. Real angular cutoffs remain real functions.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open Filter
open scoped Topology BigOperators ContDiff

theorem coordinateTransportDescendant_germ_eq_separated_words {N : ℕ} (B K : RegularJointSpace N → Fin N → ℂ) (η τ ξ : ℝ)
    (F : RegularJointSpace N → ℂ) (g : (Fin N → ℝ) → ℂ)
    (hA : ∀ i j : Fin N, ContDiff ℝ ∞ (actualBalancedInverseEntry η τ ξ i j))
    (hg : ContDiff ℝ ∞ g) (x : ℂ × (Fin N → ℝ))
    (hχ : ∀ i, ContDiffAt ℝ 2 (actualPhysicalCoordinate η τ ξ i) x)
    (hB : AnalyticAt ℂ B
      (regularJointMap (actualPhysicalCoordinate η τ ξ) x))
    (hK : ∀ j, AnalyticAt ℂ (fun p : RegularJointSpace N => K p j)
      (regularJointMap (actualPhysicalCoordinate η τ ξ) x))
    (hF : AnalyticAt ℂ F (regularJointMap (actualPhysicalCoordinate η τ ξ) x))
    (hdet : actualCoordinateDeterminant η τ ξ x ≠ 0)
    (hV : ∀ᶠ y in 𝓝 x, ∀ i, coordinateAngularVelocity B η τ ξ i y =
      -∑ j, actualBalancedInverseEntry η τ ξ i j y.2 *
        K (regularJointMap (actualPhysicalCoordinate η τ ξ) y) j)
    (n : ℕ) :
    coordinateTransportDescendant B η τ ξ
      (fun y => F (regularJointMap (actualPhysicalCoordinate η τ ξ) y) * g y.2) n =ᶠ[𝓝 x]
      coordinateSeparatedWordSum B K η τ ξ F g n := by
  have hm : ContinuousAt (regularJointMap (actualPhysicalCoordinate η τ ξ)) x :=
    continuousAt_fst.prodMk (continuousAt_pi.mpr (fun i => (hχ i).continuousAt))
  have hχnear : ∀ᶠ y in 𝓝 x, ∀ i, ContDiffAt ℝ 2 (actualPhysicalCoordinate η τ ξ i) y :=
    Filter.eventually_all.mpr (fun i => (hχ i).eventually (by norm_num))
  have hdnear : ∀ᶠ y in 𝓝 x, actualCoordinateDeterminant η τ ξ y ≠ 0 :=
    (scalarCoordinateDet_differentiableAt (actualPhysicalCoordinate η τ ξ)
      actualAngularDirection x hχ).continuousAt.eventually_ne hdet
  have hBnear := hm.eventually hB.eventually_analyticAt
  have hKnear : ∀ᶠ y in 𝓝 x, ∀ j, AnalyticAt ℂ
      (fun p : RegularJointSpace N => K p j)
      (regularJointMap (actualPhysicalCoordinate η τ ξ) y) :=
    Filter.eventually_all.mpr (fun j => hm.eventually (hK j).eventually_analyticAt)
  have hFnear := hm.eventually hF.eventually_analyticAt
  have hVnear := eventually_eventually_nhds.mpr hV
  filter_upwards [hχnear, hdnear, hBnear, hKnear, hFnear, hVnear] with y hχy hdy hBy hKy hFy hVy
  exact coordinateTransportDescendant_eq_separated_words B K η τ ξ F g hA hg y
    hχy hBy hKy hFy hdy hVy n

variable {N : ℕ}

theorem coordinateSeparatedWordSum_parameter_analyticAt (B K : RegularJointSpace N → Fin N → ℂ) (η τ ξ : ℝ)
    (F : RegularJointSpace N → ℂ) (g : (Fin N → ℝ) → ℂ) (n : ℕ)
    (θ : Fin N → ℝ) (s : ℂ) (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ) (hs : 0 < s.im)
    (hB : AnalyticAt ℂ B
      (regularJointMap (actualPhysicalCoordinate η τ ξ) (s, θ)))
    (hK : ∀ j, AnalyticAt ℂ (fun p : RegularJointSpace N => K p j)
      (regularJointMap (actualPhysicalCoordinate η τ ξ) (s, θ)))
    (hF : AnalyticAt ℂ F (regularJointMap (actualPhysicalCoordinate η τ ξ) (s, θ))) :
    AnalyticAt ℂ (fun u => coordinateSeparatedWordSum B K η τ ξ F g n (u, θ)) s := by
  apply Finset.analyticAt_fun_sum
  intro w _
  change AnalyticAt ℂ (fun u : ℂ =>
    transportAnalyticWord B
      K F n w
        (regularJointMap (actualPhysicalCoordinate η τ ξ) (u, θ)) *
      transportAngularWord (actualBalancedInverseEntry η τ ξ) g n w θ) s
  exact ((transportAnalyticWord_analyticAt _ _ _ _ hB hK hF n w).comp
    (f := fun u : ℂ => regularJointMap (actualPhysicalCoordinate η τ ξ) (u, θ))
    (actual_regular_map_parameter_analyticAt η τ ξ θ s hη hτ hξ hs)).mul analyticAt_const

theorem coordinateTransportDescendant_parameter_analyticAt (B K : RegularJointSpace N → Fin N → ℂ) (η τ ξ : ℝ)
    (F : RegularJointSpace N → ℂ) (g : (Fin N → ℝ) → ℂ)
    (hA : ∀ i j : Fin N, ContDiff ℝ ∞ (actualBalancedInverseEntry η τ ξ i j))
    (hg : ContDiff ℝ ∞ g) (θ : Fin N → ℝ) (s : ℂ)
    (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ) (hs : 0 < s.im)
    (hχ : ∀ i, ContDiffAt ℝ 2 (actualPhysicalCoordinate η τ ξ i) (s, θ))
    (hB : AnalyticAt ℂ B
      (regularJointMap (actualPhysicalCoordinate η τ ξ) (s, θ)))
    (hK : ∀ j, AnalyticAt ℂ (fun p : RegularJointSpace N => K p j)
      (regularJointMap (actualPhysicalCoordinate η τ ξ) (s, θ)))
    (hF : AnalyticAt ℂ F (regularJointMap (actualPhysicalCoordinate η τ ξ) (s, θ)))
    (hdet : actualCoordinateDeterminant η τ ξ (s, θ) ≠ 0)
    (hV : ∀ᶠ y in 𝓝 (s, θ), ∀ i, coordinateAngularVelocity B η τ ξ i y =
      -∑ j, actualBalancedInverseEntry η τ ξ i j y.2 *
        K (regularJointMap (actualPhysicalCoordinate η τ ξ) y) j)
    (n : ℕ) :
    AnalyticAt ℂ (fun u => coordinateTransportDescendant B η τ ξ
      (fun y => F (regularJointMap (actualPhysicalCoordinate η τ ξ) y) * g y.2) n (u, θ)) s := by
  have he := coordinateTransportDescendant_germ_eq_separated_words B K η τ ξ F g hA hg (s, θ)
    hχ hB hK hF hdet hV n
  have hm : ContinuousAt (fun u : ℂ => (u, θ)) s := continuousAt_id.prodMk continuousAt_const
  have he' : (fun u => coordinateTransportDescendant B η τ ξ
      (fun y => F (regularJointMap (actualPhysicalCoordinate η τ ξ) y) * g y.2) n (u, θ))
      =ᶠ[𝓝 s] (fun u => coordinateSeparatedWordSum B K η τ ξ F g n (u, θ)) := hm.eventually he
  exact (coordinateSeparatedWordSum_parameter_analyticAt B K η τ ξ F g n θ s hη hτ hξ hs hB hK hF).congr
    he'.symm


end IsingBulk.AnisoF002.Isotropic
