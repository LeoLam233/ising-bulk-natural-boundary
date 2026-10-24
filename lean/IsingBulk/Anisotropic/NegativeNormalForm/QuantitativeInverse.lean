import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
import Mathlib.Tactic

/-! Quantitative contraction representatives on specified closed balls.
These are auxiliary inverse estimates, not assumptions of a normal form. -/
noncomputable section
open Set Metric
namespace IsingBulk.Anisotropic.NegativeNormalForm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

private def identityRightInverse : (ContinuousLinearMap.id ℂ E).NonlinearRightInverse where
  toFun := id
  nnnorm := 1
  bound' x := by simp
  right_inv' x := rfl

 theorem perturbation_surjOn_closedBall (F : E → E) (r : ℝ) (hr : 0 ≤ r) (c : NNReal)
    (hF0 : F 0=0) (hLip : LipschitzOnWith c (fun x => F x-x) (closedBall 0 r)) :
    SurjOn F (closedBall 0 r) (closedBall 0 ((1-(c:ℝ))*r)) := by
  have ha : ApproximatesLinearOn F (ContinuousLinearMap.id ℂ E) (closedBall 0 r) c :=
    hLip.approximatesLinearOn
  have h := ha.surjOn_closedBall_of_nonlinearRightInverse identityRightInverse hr Subset.rfl
  simpa only [identityRightInverse,hF0,NNReal.coe_one,inv_one] using h

omit [NormedSpace ℂ E] [CompleteSpace E] in
 theorem perturbation_distance_lower (F : E → E) (s : Set E) (c : NNReal)
    (hLip : LipschitzOnWith c (fun x => F x-x) s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    (1-(c:ℝ))*‖x-y‖ ≤ ‖F x-F y‖ := by
  have he := hLip.dist_le_mul x hx y hy
  rw [dist_eq_norm,dist_eq_norm] at he
  have ht : ‖x-y‖ ≤ ‖F x-F y‖+‖(F x-x)-(F y-y)‖ := by
    calc
      _ = ‖(F x-F y)-((F x-x)-(F y-y))‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  nlinarith

omit [NormedSpace ℂ E] [CompleteSpace E] in
 theorem perturbation_injOn (F : E → E) (s : Set E) (c : NNReal) (hc : (c:ℝ)<1)
    (hLip : LipschitzOnWith c (fun x => F x-x) s) : InjOn F s := by
  intro x hx y hy hxy
  have h := perturbation_distance_lower F s c hLip hx hy
  rw [hxy,sub_self,norm_zero] at h
  have hz : ‖x-y‖=0 := by nlinarith [norm_nonneg (x-y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-- A representative is defined on a common quantitative target ball, rather
than extending a nonquantified inverse-function-theorem germ arbitrarily. -/
 theorem exists_quantitative_inverse (F : E → E) (r : ℝ) (hr : 0 ≤ r)
    (c : NNReal) (hc : (c:ℝ)<1) (hF0 : F 0=0)
    (hLip : LipschitzOnWith c (fun x => F x-x) (closedBall 0 r)) :
    ∃ V : E → E, V 0=0 ∧
      (∀ y, ‖y‖≤(1-(c:ℝ))*r → V y ∈ closedBall 0 r ∧ F (V y)=y ∧
        ‖V y‖≤‖y‖/(1-(c:ℝ))) ∧
      (∀ y z, ‖y‖≤(1-(c:ℝ))*r → ‖z‖≤(1-(c:ℝ))*r →
        ‖V y-V z‖≤‖y-z‖/(1-(c:ℝ))) := by
  have hsur := perturbation_surjOn_closedBall F r hr c hF0 hLip
  have hp : 0<1-(c:ℝ) := sub_pos.mpr hc
  have hex (y : E) (hy : ‖y‖≤(1-(c:ℝ))*r) : ∃ x ∈ closedBall 0 r, F x=y :=
    hsur (by simpa using hy)
  let V : E → E := fun y => if hy : ‖y‖≤(1-(c:ℝ))*r then (hex y hy).choose else 0
  have hV (y : E) (hy : ‖y‖≤(1-(c:ℝ))*r) : V y ∈ closedBall 0 r ∧ F (V y)=y := by
    dsimp only [V]
    rw [dite_eq_left hy]
    exact (hex y hy).choose_spec
  have h0 : ‖(0:E)‖≤(1-(c:ℝ))*r := by simp only [norm_zero]; positivity
  have hV0 : V 0=0 := perturbation_injOn F _ c hc hLip (hV 0 h0).1
    (by simpa using hr) ((hV 0 h0).2.trans hF0.symm)
  have hpair (y z : E) (hy : ‖y‖≤(1-(c:ℝ))*r) (hz : ‖z‖≤(1-(c:ℝ))*r) :
      ‖V y-V z‖≤‖y-z‖/(1-(c:ℝ)) := by
    apply (le_div_iff₀ hp).mpr
    have h := perturbation_distance_lower F _ c hLip (hV y hy).1 (hV z hz).1
    rw [(hV y hy).2,(hV z hz).2] at h
    simpa [mul_comm] using h
  refine ⟨V,hV0,?_,hpair⟩
  intro y hy
  refine ⟨(hV y hy).1,(hV y hy).2,?_⟩
  simpa [hV0] using hpair y 0 hy h0

end IsingBulk.Anisotropic.NegativeNormalForm
