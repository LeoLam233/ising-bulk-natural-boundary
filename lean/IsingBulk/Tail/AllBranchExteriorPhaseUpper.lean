import IsingBulk.Tail.AllBranchExteriorWeights
import IsingBulk.Tail.AllBranchExteriorNearNumerator
import IsingBulk.Analysis.BranchEndpoint
import Mathlib.Analysis.Calculus.MeanValue

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch Set

theorem allBranchExterior_phase_difference_upper {d : LocalBranchData} (B : BranchEstimates d)
    (ε a u v : ℝ) (hε : 0 < ε) (hεr : ε ≤ B.ε₀) (ha : 0 < a)
    (hseg : ∀ x ∈ uIcc u v, a ≤ |x| ∧ |x| ≤ B.r) :
    ‖originalPhase d ε v-originalPhase d ε u‖ ≤ (B.magnitudeUpper/Real.sqrt a)*|v-u| := by
  have hd (x : ℝ) (hx : x ∈ uIcc u v) : DifferentiableAt ℝ (originalPhase d ε) x := by
    obtain ⟨hr,hi⟩ := B.quadrant ε x hε hεr (hseg x hx).2
    exact (currentPhase_hasDerivAt d ε 0 x hr hi).differentiableAt
  have hb (x : ℝ) (hx : x ∈ uIcc u v) : ‖deriv (originalPhase d ε) x‖ ≤ B.magnitudeUpper/Real.sqrt a := by
    apply (B.magnitude ε x hε hεr (hseg x hx).2).2.trans
    exact div_le_div_of_nonneg_left B.magnitudeUpper_pos.le (Real.sqrt_pos.mpr ha)
      (Real.sqrt_le_sqrt (by linarith [(hseg x hx).1]))
  simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_deriv_le hd hb
    (convex_uIcc u v) left_mem_uIcc right_mem_uIcc

theorem allBranchExterior_common_sign_segment (a r u v : ℝ)
    (hu : |u| ≤ r) (hv : |v| ≤ r)
    (hs : (a ≤ u ∧ a ≤ v) ∨ (u ≤ -a ∧ v ≤ -a)) :
    ∀ x ∈ uIcc u v, a ≤ |x| ∧ |x| ≤ r := by
  intro x hx
  have hb : min u v ≤ x ∧ x ≤ max u v := hx
  have hlu : -r ≤ u ∧ u ≤ r := abs_le.mp hu
  have hlv : -r ≤ v ∧ v ≤ r := abs_le.mp hv
  constructor
  · rcases hs with hs|hs
    · have hxpos : a ≤ x := (le_min hs.1 hs.2).trans hb.1
      exact hxpos.trans (le_abs_self _)
    · have hxneg : x ≤ -a := hb.2.trans (max_le hs.1 hs.2)
      have hh := neg_le_abs x
      linarith
  · rw [abs_le]
    exact ⟨(le_min hlu.1 hlv.1).trans hb.1,hb.2.trans (max_le hlu.2 hlv.2)⟩

theorem allBranchExterior_common_sign_phase_diameter {N : ℕ} {d : LocalBranchData}
    (B : BranchEstimates d) (ε a : ℝ) (u : Fin N → ℝ)
    (hε : 0 < ε) (hεr : ε ≤ B.ε₀) (ha : 0 < a)
    (hu : ∀ i, |u i| ≤ B.r) (hs : (∀ i, a ≤ u i) ∨ (∀ i, u i ≤ -a)) :
    ∀ p q, ‖originalPhase d ε (u p)-originalPhase d ε (u q)‖ ≤
      (B.magnitudeUpper/Real.sqrt a)*allBranchExteriorDiameter u := by
  intro p q
  have hseg := allBranchExterior_common_sign_segment a B.r (u q) (u p) (hu q) (hu p)
    (by rcases hs with hs|hs; exact Or.inl ⟨hs q,hs p⟩; exact Or.inr ⟨hs q,hs p⟩)
  exact (allBranchExterior_phase_difference_upper B ε a (u q) (u p) hε hεr ha hseg).trans
    (mul_le_mul_of_nonneg_left (allBranchExterior_pair_le_diameter u p q) (div_nonneg B.magnitudeUpper_pos.le (Real.sqrt_nonneg _)))

end
end IsingBulk.Tail
