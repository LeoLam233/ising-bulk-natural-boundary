import IsingBulk.Tail.AllBranchExteriorTruncation
import IsingBulk.Tail.AllBranchExteriorOriginalNumerator
import IsingBulk.Tail.MicrocoreMeasure

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch IsingBulk.Jets Set Function
open scoped ContDiff

theorem allBranchExterior_truncated_source_data (d : LocalBranchData) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ n M : ℕ,
      ∀ p q : Fin (n+1), ∀ h : ℝ, 0 < h → ∀ w : (Fin (n+1) → ℝ) → ℝ,
      ContDiff ℝ ∞ w → tsupport w ⊆ microcoreCube (n+1) r →
      ContDiff ℝ ∞ (allBranchTruncatedWeight M h p q w) ∧
      HasCompactSupport (allBranchTruncatedWeight M h p q w) ∧
      ∀ u ∈ tsupport (allBranchTruncatedWeight M h p q w),
        ActualJetPoint (-d.c₀*ε) d.thetaB p q (radialParameter d.theta ε) u ∧
        AnalyticAt ℂ (unfactoredNumerator (fun t : ℂ × (Fin (n+1) → ℂ) => microRegularAmplitude t.1 t.2))
          (radialParameter d.theta ε,chartMap (-d.c₀*ε) d.thetaB (radialParameter d.theta ε) u) := by
  obtain ⟨rA,hrA,hchart⟩ := allBranchExterior_original_actual_chart d
  obtain ⟨C,rQ,_,hrQ,hnum⟩ := allBranchExterior_original_numerator_jets d 0
  let r := min rA rQ
  have hr : 0 < r := lt_min hrA hrQ
  refine ⟨r,hr,?_⟩
  intro ε hε hεr n M p q h hh w hw hsupp
  have hsub : tsupport (allBranchTruncatedWeight M h p q w) ⊆ microcoreCube (n+1) r := by
    intro u hu
    exact hsupp (allBranchTruncatedWeight_support M hh p q w hu).1
  refine ⟨allBranchTruncatedWeight_smooth M hh p q w hw,
    (microcoreCube_compact (n+1) r).of_isClosed_subset (isClosed_tsupport _) hsub,?_⟩
  intro u hu
  have hub := (mem_microcoreCube r u).mp (hsub hu)
  have hupq : u p ≠ u q := by
    have hhq := (allBranchTruncatedWeight_support M hh p q w hu).2.1
    intro heq
    rw [heq,sub_self,abs_zero] at hhq
    linarith
  have hp := hchart ε hε (hεr.trans (min_le_left _ _)) n p q u
    (fun i => (hub i).trans (min_le_left _ _)) hupq
  refine ⟨hp,?_⟩
  have hn := (hnum ε hε (hεr.trans (min_le_right _ _)) (n+1) u
    (fun i => (hub i).trans (min_le_right _ _))).analytic
  simpa only [original_chartMap_eq] using hn

end
end IsingBulk.Tail
