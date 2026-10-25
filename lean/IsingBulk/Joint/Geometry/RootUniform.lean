import IsingBulk.Joint.Geometry.RootAnalytic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Topology.Order.Compact

namespace IsingBulk.Joint
noncomputable section
open Set

@[fun_prop] theorem canonicalRoot_real_continuousAt {K : Coupling}
    (hK : K ∉ spectralSet) (q : ℝ) :
    ContinuousAt (fun v : Coupling × ℝ => canonicalRoot v.1 (v.2 : ℂ)) (K,q) := by
  have hf : ContinuousAt (fun v : Coupling × ℂ => canonicalRoot v.1 v.2) (K,(q : ℂ)) :=
    (canonicalRoot_joint_analyticAt hK q).continuousAt
  exact ContinuousAt.comp (g := fun v : Coupling × ℂ => canonicalRoot v.1 v.2)
    (f := fun v : Coupling × ℝ => (v.1,(v.2 : ℂ))) hf (by fun_prop)

theorem canonicalRoot_arccos_cos (K : Coupling) (q : ℝ) :
    canonicalRoot K ((Real.arccos (Real.cos q) : ℝ) : ℂ) = canonicalRoot K (q : ℂ) := by
  unfold canonicalRoot
  rw [← Complex.ofReal_cos,Real.cos_arccos (Real.neg_one_le_cos q) (Real.cos_le_one q),Complex.ofReal_cos]

/-- Compact coupling sets have one root modulus bound for every real angular variable. -/
theorem canonicalRoot_uniform_gap {C : Set Coupling} (hC : IsCompact C)
    (hs : C ⊆ spectralSetᶜ) : ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      ∀ K ∈ C, ∀ q : ℝ, ‖canonicalRoot K (q : ℂ)‖ ≤ r := by
  by_cases hne : C.Nonempty
  · let Q : Set (Coupling × ℝ) := C ×ˢ Icc 0 Real.pi
    have hQ : IsCompact Q := hC.prod isCompact_Icc
    have hQne : Q.Nonempty := ⟨(hne.choose,0),hne.choose_spec,by simp [Real.pi_pos.le]⟩
    have hc : ContinuousOn (fun v : Coupling × ℝ => ‖canonicalRoot v.1 (v.2 : ℂ)‖) Q := by
      intro v hv
      exact (canonicalRoot_real_continuousAt (hs hv.1) v.2).norm.continuousWithinAt
    obtain ⟨v,hv,hmax⟩ := hQ.exists_isMaxOn hQne hc
    have hr := (canonicalRoot_spec (hs hv.1) v.2).2
    let r := (‖canonicalRoot v.1 (v.2 : ℂ)‖+1)/2
    refine ⟨r,by dsimp [r]; positivity,by dsimp [r]; linarith,?_⟩
    intro K hK q
    have hm := hmax (show (K,Real.arccos (Real.cos q)) ∈ Q from
      ⟨hK,Real.arccos_nonneg _,Real.arccos_le_pi _⟩)
    change ‖canonicalRoot K (Real.arccos (Real.cos q) : ℂ)‖ ≤ ‖canonicalRoot v.1 (v.2 : ℂ)‖ at hm
    rw [canonicalRoot_arccos_cos] at hm
    exact hm.trans (by dsimp [r]; linarith)
  · refine ⟨1/2,by norm_num,by norm_num,?_⟩
    intro K hK
    exact False.elim (hne ⟨K,hK⟩)

/-- The pair-interaction denominator cannot approach zero on compact couplings. -/
theorem canonicalRoot_pair_gap {C : Set Coupling} (hC : IsCompact C)
    (hs : C ⊆ spectralSetᶜ) : ∃ δ : ℝ, 0 < δ ∧
      ∀ K ∈ C, ∀ q t : ℝ,
        δ ≤ ‖1 - canonicalRoot K (q : ℂ) * canonicalRoot K (t : ℂ)‖ := by
  obtain ⟨r,hr0,hr1,hr⟩ := canonicalRoot_uniform_gap hC hs
  refine ⟨1-r^2,by nlinarith,?_⟩
  intro K hK q t
  have hp : ‖canonicalRoot K (q : ℂ) * canonicalRoot K (t : ℂ)‖ ≤ r^2 := by
    rw [norm_mul,pow_two]
    exact mul_le_mul (hr K hK q) (hr K hK t) (norm_nonneg _) hr0.le
  have hn := norm_sub_norm_le (1 : ℂ) (canonicalRoot K (q : ℂ)*canonicalRoot K (t : ℂ))
  rw [norm_one] at hn
  linarith

end
end IsingBulk.Joint
