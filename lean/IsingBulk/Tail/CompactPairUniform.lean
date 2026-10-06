import IsingBulk.Tail.CompactLimitingGeometry
import Mathlib.Topology.Order.Compact

/-! Uniform strict constants on the source compact L/R group squares.
The group margins are selected before these constants are produced. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First Set

theorem continuousAt_canceledPair {E : Type*} [TopologicalSpace E]
    (a b z w : E → ℂ) (x : E)
    (ha : ContinuousAt a x) (hb : ContinuousAt b x)
    (hz : ContinuousAt z x) (hw : ContinuousAt w x)
    (ha0 : a x ≠ 0) (hb0 : b x ≠ 0) (hzw : 1-z x*w x ≠ 0) :
    ContinuousAt (fun t => canceledPair (a t) (b t) (z t) (w t)) x := by
  exact ((((ha.sub hb).pow 2).neg.mul hz).mul hw).div
    ((ha.mul hb).mul ((continuousAt_const.sub (hz.mul hw)).pow 2))
    (mul_ne_zero (mul_ne_zero ha0 hb0) (pow_ne_zero 2 hzw))

def limitingLeftPair (b : ℝ) (x : ℝ × ℝ) : ℂ :=
  canceledPair (limitingAngle x.1) (limitingAngle x.2)
    (compactLeftRoot (limitingAngularW b x.1:ℂ))
    (compactLeftRoot (limitingAngularW b x.2:ℂ))

def limitingRightPair (b : ℝ) (x : ℝ × ℝ) : ℂ :=
  canceledPair (limitingAngle x.1) (limitingAngle x.2)
    (interiorRoot (limitingAngularW b x.1:ℂ))
    (interiorRoot (limitingAngularW b x.2:ℂ))

theorem limitingLeftPair_continuousAt (b : ℝ) (x : ℝ × ℝ)
    (h₁ : 1 < limitingAngularW b x.1) (h₂ : 1 < limitingAngularW b x.2) :
    ContinuousAt (limitingLeftPair b) x := by
  have hy₁ : ContinuousAt (fun t : ℝ × ℝ => limitingAngle t.1) x := by unfold limitingAngle; fun_prop
  have hy₂ : ContinuousAt (fun t : ℝ × ℝ => limitingAngle t.2) x := by unfold limitingAngle; fun_prop
  have hz₁ : ContinuousAt (fun t : ℝ × ℝ => compactLeftRoot (limitingAngularW b t.1:ℂ)) x :=
    (compactLeftRoot_analyticAt (by simpa using h₁)).continuousAt.comp
      (by unfold limitingAngularW; fun_prop)
  have hz₂ : ContinuousAt (fun t : ℝ × ℝ => compactLeftRoot (limitingAngularW b t.2:ℂ)) x :=
    (compactLeftRoot_analyticAt (by simpa using h₂)).continuousAt.comp
      (by unfold limitingAngularW; fun_prop)
  apply continuousAt_canceledPair _ _ _ _ x hy₁ hy₂ hz₁ hz₂
    (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
  exact one_sub_mul_ne_zero_of_norm_lt_one
    (compactLeftRoot_norm_lt_one (by simpa using h₁))
    (compactLeftRoot_norm_lt_one (by simpa using h₂))

theorem limitingRightPair_continuousAt (b : ℝ) (x : ℝ × ℝ)
    (h₁ : |limitingAngularW b x.1| < 1) (h₂ : |limitingAngularW b x.2| < 1) :
    ContinuousAt (limitingRightPair b) x := by
  have hy₁ : ContinuousAt (fun t : ℝ × ℝ => limitingAngle t.1) x := by unfold limitingAngle; fun_prop
  have hy₂ : ContinuousAt (fun t : ℝ × ℝ => limitingAngle t.2) x := by unfold limitingAngle; fun_prop
  have hz₁ : ContinuousAt (fun t : ℝ × ℝ => interiorRoot (limitingAngularW b t.1:ℂ)) x :=
    (interiorRoot_analyticAt_compactRight (by simpa using h₁)).continuousAt.comp
      (by unfold limitingAngularW; fun_prop)
  have hz₂ : ContinuousAt (fun t : ℝ × ℝ => interiorRoot (limitingAngularW b t.2:ℂ)) x :=
    (interiorRoot_analyticAt_compactRight (by simpa using h₂)).continuousAt.comp
      (by unfold limitingAngularW; fun_prop)
  apply continuousAt_canceledPair _ _ _ _ x hy₁ hy₂ hz₁ hz₂
    (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
  obtain ⟨hn₁,hi₁⟩ := compactRight_real_norm_im _ h₁
  obtain ⟨hn₂,hi₂⟩ := compactRight_real_norm_im _ h₂
  have hs := schur_normSq_lt_of_same_half hn₁.le hn₂.le (mul_pos_of_neg_of_neg hi₁ hi₂)
  intro he
  rw [he] at hs
  simp only [map_zero] at hs
  exact (not_lt_of_ge (Complex.normSq_nonneg _)) hs

theorem compact_norm_strict_bound {E : Type*} [TopologicalSpace E]
    (K : Set E) (f : E → ℂ) (hK : IsCompact K) (hf : ContinuousOn f K)
    (hstrict : ∀ x ∈ K, ‖f x‖ < 1) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∀ x ∈ K, ‖f x‖ ≤ q := by
  by_cases hn : K.Nonempty
  · obtain ⟨x,hx,hmax⟩ := hK.exists_isMaxOn hn hf.norm
    refine ⟨(‖f x‖+1)/2,by positivity,by linarith [hstrict x hx],?_⟩
    intro y hy
    have hm : ‖f y‖ ≤ ‖f x‖ := hmax hy
    linarith [hstrict x hx]
  · exact ⟨1/2,by norm_num,by norm_num,fun x hx => False.elim (hn ⟨x,hx⟩)⟩

/-- Fixed L margins yield one q<1 for the entire closed same-group square. -/
theorem compact_left_group_uniform (s : ℂ) (b ell : ℝ)
    (hS : sourceS s=((1+Real.cos b:ℝ):ℂ)) (hb : 0 < b) (hbπ : b < Real.pi)
    (hell : 0 < ell) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∀ θ ∈ Icc (-Real.pi) (-b-ell),
      ∀ φ ∈ Icc (-Real.pi) (-b-ell), ‖limitingLeftPair b (θ,φ)‖ ≤ q := by
  let K := Icc (-Real.pi) (-b-ell) ×ˢ Icc (-Real.pi) (-b-ell)
  have hcont : ContinuousOn (limitingLeftPair b) K := by
    intro x hx
    exact (limitingLeftPair_continuousAt b x
      (limiting_left_W_gt_one b x.1 hb hbπ hx.1.1 (by linarith [hx.1.2]))
      (limiting_left_W_gt_one b x.2 hb hbπ hx.2.1 (by linarith [hx.2.2]))).continuousWithinAt
  have hstrict : ∀ x ∈ K, ‖limitingLeftPair b x‖ < 1 := by
    intro x hx
    exact limiting_left_complete_pair_strict s b x.1 x.2 hS hb hbπ hx.1.1
      (by linarith [hx.1.2]) hx.2.1 (by linarith [hx.2.2])
  obtain ⟨q,hq,hq1,hbound⟩ := compact_norm_strict_bound K _
    (isCompact_Icc.prod isCompact_Icc) hcont hstrict
  exact ⟨q,hq,hq1,fun θ hθ φ hφ => hbound (θ,φ) ⟨hθ,hφ⟩⟩

/-- Fixed R margins yield one q<1, including the common endpoint θ=φ=0. -/
theorem compact_right_group_uniform (s : ℂ) (b ell : ℝ)
    (hS : sourceS s=((1+Real.cos b:ℝ):ℂ)) (hb : 0 < b) (hbπ : b < Real.pi)
    (hell : 0 < ell) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∀ θ ∈ Icc (-b+ell) 0,
      ∀ φ ∈ Icc (-b+ell) 0, ‖limitingRightPair b (θ,φ)‖ ≤ q := by
  let K := Icc (-b+ell) 0 ×ˢ Icc (-b+ell) 0
  have hcont : ContinuousOn (limitingRightPair b) K := by
    intro x hx
    exact (limitingRightPair_continuousAt b x
      (limiting_right_W_inside b x.1 hb hbπ (by linarith [hx.1.1]) hx.1.2)
      (limiting_right_W_inside b x.2 hb hbπ (by linarith [hx.2.1]) hx.2.2)).continuousWithinAt
  have hstrict : ∀ x ∈ K, ‖limitingRightPair b x‖ < 1 := by
    intro x hx
    exact limiting_right_complete_pair_strict s b x.1 x.2 hS hb hbπ
      (by linarith [hx.1.1]) hx.1.2 (by linarith [hx.2.1]) hx.2.2
  obtain ⟨q,hq,hq1,hbound⟩ := compact_norm_strict_bound K _
    (isCompact_Icc.prod isCompact_Icc) hcont hstrict
  exact ⟨q,hq,hq1,fun θ hθ φ hφ => hbound (θ,φ) ⟨hθ,hφ⟩⟩

end
end IsingBulk.Tail
