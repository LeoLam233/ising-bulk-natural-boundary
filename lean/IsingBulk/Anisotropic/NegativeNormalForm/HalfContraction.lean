import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Set Metric

theorem exists_unique_half_contraction_fixedPoint {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (G : E → E) (a : E) {r : ℝ} (hr : 0≤r)
    (hL : LipschitzOnWith (1/2) G (closedBall a r)) (hG : ‖G a-a‖≤r/2) :
    ∃ x∈closedBall a r, G x=x ∧ ‖x-a‖≤2*‖G a-a‖ ∧
      ∀ y∈closedBall a r, G y=y → y=x := by
  have ha : a∈closedBall a r := mem_closedBall_self hr
  have hm : MapsTo G (closedBall a r) (closedBall a r) := by
    intro x hx
    have hh := hL.dist_le_mul x hx a ha
    simp only [NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat,dist_eq_norm] at hh
    have hb : ‖x-a‖≤r := by simpa only [mem_closedBall,dist_eq_norm] using hx
    change dist (G x) a≤r
    rw [dist_eq_norm]
    calc
      ‖G x-a‖≤‖G x-G a‖+‖G a-a‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ r := by linarith
  have hc : ContractingWith (1/2) (hm.restrict G (closedBall a r) (closedBall a r)) :=
    ⟨by norm_num,hL.mapsToRestrict hm⟩
  obtain ⟨x,hx,hfix,_,_⟩ := ContractingWith.exists_fixedPoint'
    isClosed_closedBall.isComplete hm hc ha (edist_ne_top _ _)
  have hfx : G x=x := hfix
  refine ⟨x,hx,hfx,?_,?_⟩
  · have hh := hL.dist_le_mul x hx a ha
    simp only [NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat,dist_eq_norm,hfx] at hh
    have ht := norm_sub_le_norm_sub_add_norm_sub x (G a) a
    linarith
  · intro y hy hfy
    have hh := hL.dist_le_mul y hy x hx
    simp only [NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat,dist_eq_norm,hfx,hfy] at hh
    exact sub_eq_zero.mp (norm_eq_zero.mp (by linarith [norm_nonneg (y-x)]))

end
end IsingBulk.Anisotropic.NegativeNormalForm
