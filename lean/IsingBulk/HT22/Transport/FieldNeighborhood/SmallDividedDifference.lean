import IsingBulk.HT22.Transport.FieldNeighborhood.PairSlopeAnalytic

namespace IsingBulk.HT22
noncomputable section
open Set Metric Geometry IsingBulk.Preferred22
set_option backward.isDefEq.respectTransparency false

theorem inverse_dslope_small (t v w : ℂ) (D : Set ℂ) (C H d : ℝ)
    (hC : 0≤C) (_hH : 0≤H) (hd : 0≤d) (hdH : d≤H)
    (hD : Convex ℝ D) (hv : v∈D) (hw : w∈D) (hvw : ‖v-w‖≤3*d)
    (hU : ∀ q∈D, AnalyticAt ℂ (fun z : ℂ × ℂ => regularInverse z.1 z.2) (t,q))
    (hjet : ∀ q∈D, ‖fderiv ℂ (fun z : ℂ × ℂ => sourceInverseV z.1 z.2) (t,q)‖≤C)
    (hbase : ‖sourceInverseV t w‖≤2*C*H) :
    ‖dslope (regularInverse t) w v‖≤5*C*H := by
  let S := D∩closedBall w (3*d)
  have hS : Convex ℝ S := hD.inter (convex_closedBall _ _)
  have hvS : v∈S := ⟨hv,by simpa only [mem_closedBall,dist_eq_norm] using hvw⟩
  have hwS : w∈S := ⟨hw,mem_closedBall_self (by positivity)⟩
  apply norm_dslope_le_on_convex (regularInverse t) S (5*C*H) hS _ _ v w hvS hwS
  · intro q hq
    exact (AnalyticAt.comp (f := fun a : ℂ => (t,a))
      (g := fun z : ℂ × ℂ => regularInverse z.1 z.2) (hU q hq.1)
      (analyticAt_const.prod analyticAt_id)).differentiableAt
  · intro q hq
    have hh := inverseV_pair_lipschitz t w q D C hD hw hq.1 hU hjet
    have hqdist : ‖q-w‖≤3*d := by simpa only [mem_closedBall,dist_eq_norm] using hq.2
    have hbound := hh.trans (mul_le_mul_of_nonneg_left hqdist hC)
    have htri := norm_sub_le (sourceInverseV t q-sourceInverseV t w) (-sourceInverseV t w)
    simp only [sub_neg_eq_add,sub_add_cancel,norm_neg] at htri
    change ‖sourceInverseV t q‖≤5*C*H
    nlinarith [mul_le_mul_of_nonneg_left hdH hC]

end
end IsingBulk.HT22
