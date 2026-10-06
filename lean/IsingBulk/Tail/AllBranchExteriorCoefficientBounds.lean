import IsingBulk.Tail.AllBranchExteriorOriginalNumerator
import IsingBulk.Analysis.JetsUniform

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch IsingBulk.Jets IsingBulk.First Set

theorem allBranchExterior_original_coefficients (d : LocalBranchData) (j k : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r →
      ∀ N : ℕ, 1 ≤ N → ∀ p q : Fin N, p ≠ q →
        (sourceJetTerms p q j).length ≤ C*N^C ∧
        ∀ u : Fin N → ℝ, (∀ i, |u i| ≤ r) → ∀ T ∈ sourceJetTerms p q j,
          JetBound T.regularPart (radialParameter d.theta ε,fun i => originalPhase d ε (u i)) k
            ((C:ℝ)*(N:ℝ)^C) := by
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
  obtain ⟨C,hC,U,P,hU,hsU,hP,hsP,hcoeff⟩ := sourceJetTerms_uniform s₀ (Real.cos d.thetaB) hs₀ hS hc j k
  obtain ⟨rU,hrU,hsubU⟩ := Metric.isOpen_iff.mp hU (s₀,0) hsU
  obtain ⟨rP,hrP,hsubP⟩ := Metric.isOpen_iff.mp hP (s₀,0,0) hsP
  let R := min rU rP
  have hR : 0 < R := lt_min hrU hrP
  obtain ⟨rφ,Cφ,hrφ,_,hφ⟩ := original_phase_small_radius d R hR
  let r := min R rφ/2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrR : r < R := (half_lt_self (lt_min hR hrφ)).trans_le (min_le_left _ _)
  have hrφ' : r < rφ := (half_lt_self (lt_min hR hrφ)).trans_le (min_le_right _ _)
  refine ⟨C,hC,r,hr,?_⟩
  intro ε hε hεr N hN p q hpq
  obtain ⟨hcount,hreg⟩ := hcoeff N hN p q hpq
  refine ⟨hcount,?_⟩
  intro u hu T hT
  have hs : ‖radialParameter d.theta ε-s₀‖ < R := by
    rw [radialParameter_sub_zero_norm d.theta ε hε.le]
    exact hεr.trans_lt hrR
  have hphase (i : Fin N) : ‖originalPhase d ε (u i)‖ < R :=
    (hφ ε r (u i) hε hεr hrφ' (hu i)).2
  apply (hreg (radialParameter d.theta ε,fun i => originalPhase d ε (u i)) ?_ ?_).2 T hT
  · intro i
    apply hsubU
    simpa [Metric.mem_ball,Prod.dist_eq,dist_eq_norm] using
      And.intro (hs.trans_le (min_le_left _ _)) ((hphase i).trans_le (min_le_left _ _))
  · apply hsubP
    simpa [Metric.mem_ball,Prod.dist_eq,dist_eq_norm] using
      And.intro (hs.trans_le (min_le_right _ _))
        (And.intro ((hphase p).trans_le (min_le_right _ _)) ((hphase q).trans_le (min_le_right _ _)))

end
end IsingBulk.Tail
