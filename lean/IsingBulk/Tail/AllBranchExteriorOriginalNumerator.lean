import IsingBulk.Tail.AllBranchExteriorPoint
import IsingBulk.Tail.AllBranchExteriorNumerator
import IsingBulk.Tail.MicrocorePhaseNeighborhood
import IsingBulk.Tail.OriginalMicrocoreChart

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch IsingBulk.Jets IsingBulk.First

theorem allBranchExterior_original_numerator_jets (d : LocalBranchData) (J : ℕ) :
    ∃ C r : ℝ, 1 ≤ C ∧ 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r →
      ∀ N : ℕ, ∀ u : Fin N → ℝ, (∀ i, |u i| ≤ r) →
      JetBound (unfactoredNumerator (fun t : ℂ × (Fin N → ℂ) => microRegularAmplitude t.1 t.2))
        (radialParameter d.theta ε,fun i => originalPhase d ε (u i)) J
        ((2:ℝ)^J*((2:ℝ)^J*((2^J*C)^N+(2^J*C)^N)*
          (C^J*((N.choose 2:ℝ)+1)^J*(1/2:ℝ)^((N.choose 2:ℤ)-(J:ℤ))))*(2^J*C)^N) := by
  let s₀ := radialParameter d.theta 0
  have hs₀ : s₀ ≠ 0 := by
    apply norm_ne_zero_iff.mp
    change ‖radialParameter d.theta 0‖ ≠ 0
    rw [radialParameter_norm (by norm_num)]
    norm_num
  have hS : s₀+s₀⁻¹=(1+(Real.cos d.thetaB:ℂ)) := by
    simpa [IsingBulk.First.sourceS,s₀] using sourceS_radial_zero_branch d
  have hc : |Real.cos d.thetaB| < 1 := by
    have hs : 0 < Real.sin d.thetaB := d.a_pos
    have hh := Real.sin_sq_add_cos_sq d.thetaB
    rw [abs_lt]
    constructor <;> nlinarith [Real.cos_le_one d.thetaB,Real.neg_one_le_cos d.thetaB]
  obtain ⟨C,R,hC,hR,hnum⟩ := allBranchExterior_numerator_uniform s₀ (Real.cos d.thetaB)
    (1/2) hs₀ hS hc (by norm_num) (by norm_num) J
  obtain ⟨rφ,Cφ,hrφ,_,hφ⟩ := original_phase_small_radius d R hR
  let r := min R rφ/2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrR : r < R := (half_lt_self (lt_min hR hrφ)).trans_le (min_le_left _ _)
  have hrφ' : r < rφ := (half_lt_self (lt_min hR hrφ)).trans_le (min_le_right _ _)
  refine ⟨C,r,hC,hr,?_⟩
  intro ε hε hεr N u hu
  apply hnum N
  · rw [radialParameter_sub_zero_norm d.theta ε hε.le]
    exact hεr.trans_lt hrR
  · intro i
    exact (hφ ε r (u i) hε hεr hrφ' (hu i)).2

end
end IsingBulk.Tail
