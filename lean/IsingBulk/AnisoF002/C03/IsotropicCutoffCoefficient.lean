import IsingBulk.AnisoF002.C03.IsotropicActualTransportBalls

/-!
# The analytic coefficient when transport differentiates a real cutoff

The coefficient is the actual inverse-coordinate parameter slope plus
the actual coordinate slope times the covariance field. Both slopes
are differentiated from the same explicit F002 inverse.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric

def jointCoordinateDerivative (U : ℂ × ℂ → ℂ) (q : ℂ × ℂ) : ℂ :=
  deriv (fun v => U (q.1, v)) q.2

theorem jointCoordinateDerivative_analyticAt (U : ℂ × ℂ → ℂ) (q : ℂ × ℂ)
    (hU : AnalyticAt ℂ U q) : AnalyticAt ℂ (jointCoordinateDerivative U) q := by
  have hL : AnalyticAt ℂ (fun p => fderiv ℂ U p ((0, 1) : ℂ × ℂ)) q :=
    ((ContinuousLinearMap.apply ℂ ℂ ((0, 1) : ℂ × ℂ)).analyticAt _).comp hU.fderiv
  apply hL.congr
  filter_upwards [hU.eventually_analyticAt] with p hp
  exact (hp.differentiableAt.hasFDerivAt.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))).deriv.symm

theorem jointParameterDerivative_norm_le (U : ℂ × ℂ → ℂ) (q : ℂ × ℂ)
    (hU : DifferentiableAt ℂ U q) :
    ‖jointParameterDerivative U q‖ ≤ ‖fderiv ℂ U q‖ := by
  have he := (hU.hasFDerivAt.comp_hasDerivAt q.1
    ((hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2))).deriv
  change deriv (fun z => U (z, q.2)) q.1 = fderiv ℂ U q (1, 0) at he
  rw [jointParameterDerivative, he]
  simpa only [Prod.norm_def, norm_one, norm_zero, max_eq_left zero_le_one, mul_one] using
    (fderiv ℂ U q).le_opNorm ((1, 0) : ℂ × ℂ)

theorem jointCoordinateDerivative_norm_le (U : ℂ × ℂ → ℂ) (q : ℂ × ℂ)
    (hU : DifferentiableAt ℂ U q) :
    ‖jointCoordinateDerivative U q‖ ≤ ‖fderiv ℂ U q‖ := by
  have he := (hU.hasFDerivAt.comp_hasDerivAt q.2
    ((hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2))).deriv
  change deriv (fun z => U (q.1, z)) q.2 = fderiv ℂ U q (0, 1) at he
  rw [jointCoordinateDerivative, he]
  simpa only [Prod.norm_def, norm_one, norm_zero, max_eq_right zero_le_one, mul_one] using
    (fderiv ℂ U q).le_opNorm ((0, 1) : ℂ × ℂ)

def rightCutoffTransportCoefficient {N : ℕ} (p : RegularJointSpace N) (j : Fin N) : ℂ :=
  jointParameterDerivative explicitRightInverse (p.1, p.2 j) +
    jointCoordinateDerivative explicitRightInverse (p.1, p.2 j) * rightCovarianceField p.1 p.2 j

theorem rightCutoffTransportCoefficient_analyticAt {N : ℕ} (p : RegularJointSpace N)
    (j : Fin N) (hU : AnalyticAt ℂ explicitRightInverse (p.1, p.2 j))
    (hB : AnalyticAt ℂ (fun q : RegularJointSpace N => rightCovarianceField q.1 q.2) p) :
    AnalyticAt ℂ (fun q => rightCutoffTransportCoefficient q j) p := by
  have hm : AnalyticAt ℂ (fun q : RegularJointSpace N => (q.1, q.2 j)) p :=
    analyticAt_fst.prod (coordinate_analyticAt p j)
  have hS := (jointParameterDerivative_analyticAt _ _ hU).comp
    (f := fun q : RegularJointSpace N => (q.1, q.2 j)) hm
  have hv := (jointCoordinateDerivative_analyticAt _ _ hU).comp
    (f := fun q : RegularJointSpace N => (q.1, q.2 j)) hm
  have hBj : AnalyticAt ℂ (fun q : RegularJointSpace N => rightCovarianceField q.1 q.2 j) p :=
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) j).analyticAt _).comp hB
  exact hS.add (hv.mul hBj)

theorem rightCutoffTransportCoefficient_norm_le {N : ℕ} (p : RegularJointSpace N)
    (j : Fin N) (C L : ℝ) (hC : 0 ≤ C)
    (hU : DifferentiableAt ℂ explicitRightInverse (p.1, p.2 j))
    (hDU : ‖fderiv ℂ explicitRightInverse (p.1, p.2 j)‖ ≤ C)
    (hB : ‖rightCovarianceField p.1 p.2‖ ≤ L) :
    ‖rightCutoffTransportCoefficient p j‖ ≤ C * (1 + L) := by
  have hS := (jointParameterDerivative_norm_le _ _ hU).trans hDU
  have hv := (jointCoordinateDerivative_norm_le _ _ hU).trans hDU
  have hBj := (norm_le_pi_norm (rightCovarianceField p.1 p.2) j).trans hB
  calc
    _ ≤ ‖jointParameterDerivative explicitRightInverse (p.1, p.2 j)‖ +
        ‖jointCoordinateDerivative explicitRightInverse (p.1, p.2 j)‖ *
          ‖rightCovarianceField p.1 p.2 j‖ := by
      simpa only [rightCutoffTransportCoefficient, norm_mul] using norm_add_le
        (jointParameterDerivative explicitRightInverse (p.1, p.2 j))
        (jointCoordinateDerivative explicitRightInverse (p.1, p.2 j) * rightCovarianceField p.1 p.2 j)
    _ ≤ C + C * L := add_le_add hS (mul_le_mul hv hBj (norm_nonneg _) hC)
    _ = _ := by ring

theorem exists_right_inverse_first_slope_control (S : ℝ) (hS : 0 < S ∧ S < 2) :
    ∃ R C : ℝ, 0 < R ∧ 0 < C ∧
      ∀ (N : ℕ) (p : RegularJointSpace N), p ∈ rightProductDomain S R N →
        ∀ i : Fin N, AnalyticAt ℂ explicitRightInverse (p.1, p.2 i) ∧
          ‖fderiv ℂ explicitRightInverse (p.1, p.2 i)‖ ≤ C := by
  obtain ⟨R, _, hR, _, _, _, hU, _, hjets⟩ :=
    exists_right_inverse_common_convex_neighborhood S hS
  obtain ⟨C₀, hC₀⟩ := hjets 1
  refine ⟨R, max 1 C₀, hR, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro N p hp i
  have hpi : (p.1, p.2 i) ∈ cthickening R (rightParameterSegment S) :=
    thickening_subset_cthickening R _ (rightSingle_of_thickening hp.1 (hp.2 i))
  refine ⟨hU _ hpi, ?_⟩
  have hh := hC₀ _ hpi
  rw [norm_iteratedFDeriv_one] at hh
  exact hh.trans (le_max_right _ _)

end IsingBulk.AnisoF002.Isotropic
