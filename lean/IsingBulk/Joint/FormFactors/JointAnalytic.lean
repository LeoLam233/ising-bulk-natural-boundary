import IsingBulk.Joint.FormFactors.AnnularHolomorphy
import IsingBulk.Anisotropic.FormFactors.JointAnalytic

namespace IsingBulk.Joint.FormFactors
noncomputable section
open IsingBulk.First IsingBulk.Anisotropic.FormFactors
open scoped BigOperators

theorem fullDensity_joint_analyticAt (N : ℕ) (hN : 0 < N) {r : ℝ}
    {z : Coupling} {x y : Fin N → ℂ} (h : ContourAnnulus z r)
    (hx : ∀ i, r ≤ ‖x i‖ ∧ ‖x i‖ < 1) (hy : ∀ i, r ≤ ‖y i‖ ∧ ‖y i‖ < 1) :
    AnalyticAt ℂ (fun p : Coupling × ((Fin N → ℂ) × (Fin N → ℂ)) =>
      fullDensity p.1 p.2.1 p.2.2) (z,(x,y)) := by
  let p := (z,(x,y))
  have dz : AnalyticAt ℂ (fun q : Coupling × ((Fin N → ℂ) × (Fin N → ℂ)) => q.1.1) p :=
    analyticAt_fst.comp analyticAt_fst
  have dw : AnalyticAt ℂ (fun q : Coupling × ((Fin N → ℂ) × (Fin N → ℂ)) => q.1.2) p :=
    analyticAt_snd.comp analyticAt_fst
  have dx (i : Fin N) : AnalyticAt ℂ (fun q : Coupling × ((Fin N → ℂ) × (Fin N → ℂ)) => q.2.1 i) p :=
    (ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ).analyticAt _ |>.comp (analyticAt_fst.comp analyticAt_snd)
  have dy (i : Fin N) : AnalyticAt ℂ (fun q : Coupling × ((Fin N → ℂ) × (Fin N → ℂ)) => q.2.2 i) p :=
    (ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ).analyticAt _ |>.comp (analyticAt_snd.comp analyticAt_snd)
  have hx0 (i) : x i ≠ 0 := norm_pos_iff.mp (h.1.trans_le (hx i).1)
  have hy0 (i) : y i ≠ 0 := norm_pos_iff.mp (h.1.trans_le (hy i).1)
  have dX := Finset.univ.analyticAt_fun_prod (fun i _ => dx i)
  have dY := Finset.univ.analyticAt_fun_prod (fun i _ => dy i)
  have dPX := pairProduct_analyticAt_family dx (fun i j =>
    one_sub_mul_ne_zero_of_norm_lt_one (hx i).2 (hx j).2)
  have dPY := pairProduct_analyticAt_family dy (fun i j =>
    one_sub_mul_ne_zero_of_norm_lt_one (hy i).2 (hy j).2)
  have dD : AnalyticAt ℂ (fun q : Coupling × ((Fin N → ℂ) × (Fin N → ℂ)) =>
      ∏ i, (dispersion q.1 (q.2.1 i) (q.2.2 i))⁻¹) p := by
    apply Finset.univ.analyticAt_fun_prod
    intro i _
    apply AnalyticAt.inv
    · unfold dispersion dispersionPolynomial A S T
      exact (((Complex.analyticAt_cosh.comp dz).mul (Complex.analyticAt_cosh.comp dw)).sub
        (((Complex.analyticAt_sinh.comp dz).div_const).mul ((dx i).add ((dx i).inv (hx0 i))))).sub
        (((Complex.analyticAt_sinh.comp dw).div_const).mul ((dy i).add ((dy i).inv (hy0 i))))
    · exact h.2.2 _ _ (hx i).1 (hx i).2.le (hy i).1 (hy i).2.le
  have dnum := ((analyticAt_const (v := (1 : ℂ))).add dX).mul ((analyticAt_const (v := (1 : ℂ))).add dY)
  have dden := ((dX.mul dY).mul ((analyticAt_const (v := (1 : ℂ))).sub dX)).mul ((analyticAt_const (v := (1 : ℂ))).sub dY)
  have dn : coordinateProduct x * coordinateProduct y * (1-coordinateProduct x) *
      (1-coordinateProduct y) ≠ 0 := mul_ne_zero (mul_ne_zero
      (mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => hx0 i))
        (Finset.prod_ne_zero_iff.mpr (fun i _ => hy0 i)))
      (one_sub_coordinateProduct_ne_zero hN (fun i => (hx i).2)))
      (one_sub_coordinateProduct_ne_zero hN (fun i => (hy i).2))
  exact (dnum.div dden dn).mul ((dPX.mul dPY).mul dD)
end
end IsingBulk.Joint.FormFactors
