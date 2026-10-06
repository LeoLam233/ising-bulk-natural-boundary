import IsingBulk.Tail.AllBranchExteriorGuardedWeights
import IsingBulk.Tail.AllBranchExteriorTruncatedNormalForm

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets IsingBulk.Lie MeasureTheory Set Function
open scoped ContDiff

def allBranchSingleTruncatedWeight {N : ℕ} (M : ℕ) (h : ℝ) (p q : Fin N)
    (w : (Fin N → ℝ) → ℝ) (u : Fin N → ℝ) : ℝ := w u*allBranchGuardedPairWeight M h p q u

theorem allBranchSingleTruncatedWeight_smooth {N : ℕ} (M : ℕ) {h : ℝ} (hh : 0 < h)
    (p q : Fin N) (w : (Fin N → ℝ) → ℝ) (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (allBranchSingleTruncatedWeight M h p q w) :=
  hw.mul (allBranchGuardedPairWeight_smooth M hh p q)

theorem allBranchSingleTruncatedWeight_support {N : ℕ} (M : ℕ) {h : ℝ} (hh : 0 < h)
    (p q : Fin N) (w : (Fin N → ℝ) → ℝ) {u : Fin N → ℝ}
    (hu : u ∈ tsupport (allBranchSingleTruncatedWeight M h p q w)) :
    u ∈ tsupport w ∧ h/2 ≤ |u p-u q| :=
  ⟨tsupport_mul_subset_left hu,allBranchGuardedPairWeight_tsupport M hh p q (tsupport_mul_subset_right hu)⟩

theorem allBranchExterior_single_truncated_normal_form (d : LocalBranchData) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ n M : ℕ,
      ∀ p q : Fin (n+1), p ≠ q → ∀ h : ℝ, 0 < h → ∀ w : AngularSpace n → ℝ,
      ContDiff ℝ ∞ w → tsupport w ⊆ microcoreCube (n+1) r → ∀ j : ℕ,
      let W := allBranchSingleTruncatedWeight M h p q w
      iteratedDeriv j (allBranchOriginalWeightedIntegral n d ε W) (radialParameter d.theta ε) =
        ((n+1).factorial:ℂ)⁻¹*∫ u : AngularSpace n,
          sourceTermSum p q (-d.c₀*ε) d.thetaB W
            (unfactoredNumerator (fun t : ℂ × (Fin (n+1) → ℂ) => microRegularAmplitude t.1 t.2)) j
            (radialParameter d.theta ε) u := by
  obtain ⟨rA,hrA,hchart⟩ := allBranchExterior_original_actual_chart d
  obtain ⟨C,rQ,_,hrQ,hnum⟩ := allBranchExterior_original_numerator_jets d 0
  let r := min rA rQ
  have hr : 0 < r := lt_min hrA hrQ
  refine ⟨r,hr,?_⟩
  intro ε hε hεr n M p q hpq h hh w hw hsupp j
  let W := allBranchSingleTruncatedWeight M h p q w
  have hsub : tsupport W ⊆ microcoreCube (n+1) r := by
    intro u hu
    exact hsupp (allBranchSingleTruncatedWeight_support M hh p q w hu).1
  have hcompact : HasCompactSupport W :=
    (microcoreCube_compact (n+1) r).of_isClosed_subset (isClosed_tsupport _) hsub
  have hpoint (u : AngularSpace n) (hu : u ∈ tsupport W) :
      ActualJetPoint (-d.c₀*ε) d.thetaB p q (radialParameter d.theta ε) u ∧
      AnalyticAt ℂ (unfactoredNumerator (fun t : ℂ × (Fin (n+1) → ℂ) => microRegularAmplitude t.1 t.2))
        (radialParameter d.theta ε,chartMap (-d.c₀*ε) d.thetaB (radialParameter d.theta ε) u) := by
    have hub := (mem_microcoreCube r u).mp (hsub hu)
    have hupq : u p ≠ u q := by
      have hδ := (allBranchSingleTruncatedWeight_support M hh p q w hu).2
      intro he
      rw [he,sub_self,abs_zero] at hδ
      linarith
    refine ⟨hchart ε hε (hεr.trans (min_le_left _ _)) n p q u
      (fun i => (hub i).trans (min_le_left _ _)) hupq,?_⟩
    have hn := (hnum ε hε (hεr.trans (min_le_right _ _)) (n+1) u
      (fun i => (hub i).trans (min_le_right _ _))).analytic
    simpa only [original_chartMap_eq] using hn
  exact allBranchExterior_compact_source_normal_form d ε hε p q hpq W
    (allBranchSingleTruncatedWeight_smooth M hh p q w hw) hcompact _
    (fun u hu => (hpoint u hu).1) (fun u hu => (hpoint u hu).2) j

end
end IsingBulk.Tail
