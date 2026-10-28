import IsingBulk.HT22.Transport.FieldNeighborhood.CompactInputs

/-! # Recovering all base pair bounds from original inverse geometry -/
namespace IsingBulk.HT22
noncomputable section
open Set Metric Geometry
set_option backward.isDefEq.respectTransparency false

/-- Joint one-body first jets bound same-parameter differences. -/
theorem jointFunction_pair_lipschitz (F : ℂ × ℂ → ℂ) (t v w : ℂ)
    (D : Set ℂ) (C : ℝ) (hD : Convex ℝ D) (hv : v∈D) (hw : w∈D)
    (hF : ∀ q∈D, DifferentiableAt ℂ F (t,q))
    (hjet : ∀ q∈D, ‖fderiv ℂ F (t,q)‖≤C) :
    ‖F (t,w)-F (t,v)‖≤C*‖w-v‖ := by
  let S : Set (ℂ × ℂ) := {t} ×ˢ D
  have hS : Convex ℝ S := (convex_singleton t).prod hD
  have hs : ∀ z∈S, HasFDerivWithinAt F (fderiv ℂ F z) S z := by
    rintro ⟨s,q⟩ ⟨hs,hq⟩
    have he : s=t := hs
    subst s
    exact (hF q hq).hasFDerivAt.hasFDerivWithinAt
  have hb : ∀ z∈S, ‖fderiv ℂ F z‖≤C := by
    rintro ⟨s,q⟩ ⟨hs,hq⟩
    have he : s=t := hs
    subst s
    exact hjet q hq
  have hh := hS.norm_image_sub_le_of_norm_hasFDerivWithin_le hs hb
    (show (t,v)∈S from ⟨rfl,hv⟩) (show (t,w)∈S from ⟨rfl,hw⟩)
  simpa only [Prod.mk_sub_mk, sub_self, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)] using hh

/-- Bounded first joint inverse-V jets give the base E difference. -/
theorem inverseV_pair_lipschitz (t v w : ℂ) (D : Set ℂ) (C : ℝ)
    (hD : Convex ℝ D) (hv : v∈D) (hw : w∈D)
    (hU : ∀ q∈D, AnalyticAt ℂ (fun z : ℂ × ℂ => regularInverse z.1 z.2) (t,q))
    (hjet : ∀ q∈D, ‖fderiv ℂ (fun z : ℂ × ℂ => sourceInverseV z.1 z.2) (t,q)‖≤C) :
    ‖sourceInverseV t w-sourceInverseV t v‖≤C*‖w-v‖ :=
  jointFunction_pair_lipschitz _ t v w D C hD hv hw
    (fun q hq => (inverseV_joint_analytic t q (hU q hq)).differentiableAt) hjet

/-- A small base Uv and bounded original Uv jets on the convex domain give
the improved D difference, rather than the weaker O(d) estimate. -/
theorem regularInverse_pair_small (t v w : ℂ) (D : Set ℂ) (C H d : ℝ)
    (hC : 0≤C) (hH : 0≤H) (hd : 0≤d) (hdH : d≤H)
    (hD : Convex ℝ D) (hv : v∈D) (hw : w∈D) (hvw : ‖w-v‖≤d)
    (hU : ∀ q∈D, AnalyticAt ℂ (fun z : ℂ × ℂ => regularInverse z.1 z.2) (t,q))
    (hjet : ∀ q∈D, ‖fderiv ℂ (fun z : ℂ × ℂ => sourceInverseV z.1 z.2) (t,q)‖≤C)
    (hbase : ‖sourceInverseV t v‖≤C*H) :
    ‖regularInverse t w-regularInverse t v‖≤2*C*H*d := by
  let S := D∩closedBall v d
  have hS : Convex ℝ S := hD.inter (convex_closedBall v d)
  have hq (q : ℂ) (hq : q∈S) : ‖sourceInverseV t q‖≤2*C*H := by
    have hdiff := inverseV_pair_lipschitz t v q D C hD hv hq.1 hU hjet
    have hdist : ‖q-v‖≤d := by simpa only [mem_closedBall, dist_eq_norm] using hq.2
    have htri := norm_sub_le (sourceInverseV t q-sourceInverseV t v) (-sourceInverseV t v)
    simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at htri
    have hh := hdiff.trans (mul_le_mul_of_nonneg_left (hdist.trans hdH) hC)
    linarith
  have hder (q : ℂ) (hq : q∈S) : HasDerivWithinAt (regularInverse t) (sourceInverseV t q) S q := by
    have ha := AnalyticAt.comp (f := fun u : ℂ => (t,u))
      (g := fun z : ℂ × ℂ => regularInverse z.1 z.2) (hU q hq.1)
      (analyticAt_const.prod analyticAt_id)
    exact ha.differentiableAt.hasDerivAt.hasDerivWithinAt
  have hh := hS.norm_image_sub_le_of_norm_hasDerivWithin_le hder hq
    (show v∈S from ⟨hv,mem_closedBall_self hd⟩)
    (show w∈S from ⟨hw,by simpa only [mem_closedBall, dist_eq_norm] using hvw⟩)
  exact hh.trans (mul_le_mul_of_nonneg_left hvw (by positivity))

end
end IsingBulk.HT22
