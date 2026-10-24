import IsingBulk.Anisotropic.FormFactors.PairCancellation
import IsingBulk.Anisotropic.FormFactors.JointAnalytic

namespace IsingBulk.Anisotropic.FormFactors
noncomputable section
open IsingBulk.First IsingBulk.Tail
open scoped BigOperators

def anisotropicCanceledPairs {N : ℕ} (B : ℝ) (u y : Fin N → ℂ) : ℂ :=
  ∏ i, ∏ j ∈ Finset.univ.filter (fun j => i<j), (B:ℂ)*canceledPair (y i) (y j) (u i) (u j)

def canceledLatticeDensity {N : ℕ} (B C : ℝ) (S : ℂ) (y : Fin N → ℂ) (v : ℤ × ℤ) : ℂ :=
  let u := fun i => realContourRoot B C (y i)
  anisotropicCanceledPairs B u y *
    (∏ i, 2*u i/(S*y i*(1-u i*u i))) *
    (coordinateProduct u)^v.1.natAbs * (coordinateProduct y)^v.2.natAbs

theorem pairProducts_eq_anisotropicCanceledPairs {N : ℕ} {B C r : ℝ}
    (hB : 0 ≤ B) (hr : 0 < r) (hr1 : r < 1) (hm : (B+1)*(1+r⁻¹)/2 < C)
    (y : Fin N → ℂ) (hy : ∀ i,‖y i‖=r) :
    IsingBulk.First.pairProduct (fun i => realContourRoot B C (y i))*IsingBulk.First.pairProduct y =
      anisotropicCanceledPairs B (fun i => realContourRoot B C (y i)) y := by
  unfold IsingBulk.First.pairProduct anisotropicCanceledPairs
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun j _ => realContourRoot_pair_cancellation hB hr hr1 hm (hy i) (hy j))

theorem latticeClearedNumerator_eq_canceled {N : ℕ} {lam B C r : ℝ} {z : ℂ}
    (hB : 0 ≤ B) (hr : 0 < r) (hr1 : r < 1) (hm : (B+1)*(1+r⁻¹)/2 < C)
    (y : Fin N → ℂ) (hy : ∀ i,‖y i‖=r) (v : ℤ × ℤ) :
    latticeClearedNumerator lam z y (fun i => realContourRoot B C (y i))
      (fun i => realContourRoot B C (y i)) v = canceledLatticeDensity B C (spectralS z) y v := by
  unfold latticeClearedNumerator canceledLatticeDensity
  rw [pairProducts_eq_anisotropicCanceledPairs hB hr hr1 hm y hy]

theorem canceledLatticeDensity_analyticAt {N : ℕ} {B C : ℝ} {S : ℂ} (hS : S ≠ 0)
    {y : Fin N → ℂ} (hy : ∀ i,y i ≠ 0) (hW : ∀ i,1 < (realContourW B C (y i)).re)
    (v : ℤ × ℤ) : AnalyticAt ℂ (fun y : Fin N → ℂ => canceledLatticeDensity B C S y v) y := by
  have dy (i : Fin N) : AnalyticAt ℂ (fun y : Fin N → ℂ => y i) y :=
    (ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ).analyticAt y
  have du (i : Fin N) : AnalyticAt ℂ (fun y : Fin N → ℂ => realContourRoot B C (y i)) y := by
    apply (compactLeftRoot_analyticAt (hW i)).comp (f := fun y : Fin N → ℂ => realContourW B C (y i))
    exact analyticAt_const.sub (analyticAt_const.mul (((dy i).add ((dy i).inv (hy i))).div_const))
  have hun (i) : ‖realContourRoot B C (y i)‖ < 1 := compactLeftRoot_norm_lt_one (hW i)
  have hpair (i j : Fin N) : AnalyticAt ℂ (fun y : Fin N → ℂ =>
      (B:ℂ)*canceledPair (y i) (y j) (realContourRoot B C (y i)) (realContourRoot B C (y j))) y := by
    unfold canceledPair
    apply analyticAt_const.mul
    apply AnalyticAt.div
    · exact (((dy i).sub (dy j)).pow 2).neg.mul (du i) |>.mul (du j)
    · exact ((dy i).mul (dy j)).mul ((analyticAt_const.sub ((du i).mul (du j))).pow 2)
    · exact mul_ne_zero (mul_ne_zero (hy i) (hy j))
        (pow_ne_zero _ (one_sub_mul_ne_zero_of_norm_lt_one (hun i) (hun j)))
  have dP : AnalyticAt ℂ (fun y : Fin N → ℂ =>
      anisotropicCanceledPairs B (fun i => realContourRoot B C (y i)) y) y :=
    Finset.univ.analyticAt_fun_prod (fun i _ =>
      (Finset.univ.filter (fun j => i<j)).analyticAt_fun_prod (fun j _ => hpair i j))
  have dR : AnalyticAt ℂ (fun y : Fin N → ℂ => ∏ i,
      2*realContourRoot B C (y i)/(S*y i*(1-realContourRoot B C (y i)*realContourRoot B C (y i)))) y := by
    apply Finset.univ.analyticAt_fun_prod
    intro i _
    exact (analyticAt_const.mul (du i)).div
      ((analyticAt_const.mul (dy i)).mul (analyticAt_const.sub ((du i).mul (du i))))
      (mul_ne_zero (mul_ne_zero hS (hy i)) (one_sub_mul_ne_zero_of_norm_lt_one (hun i) (hun i)))
  exact ((dP.mul dR).mul ((Finset.univ.analyticAt_fun_prod (fun i _ => du i)).pow _)).mul
    ((Finset.univ.analyticAt_fun_prod (fun i _ => dy i)).pow _)
end
end IsingBulk.Anisotropic.FormFactors
