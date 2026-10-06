import IsingBulk.Tail.MicrocoreParameterBudget
import IsingBulk.Tail.MicrocoreFrozenAllOrder

/-! Pointwise cost of the actual generated terms, before arclength integration. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets IsingBulk.Lie
open scoped BigOperators

theorem norm_list_sum_le_length_mul (L : List ℂ) (B : ℝ)
    (h : ∀ z ∈ L, ‖z‖ ≤ B) : ‖L.sum‖ ≤ (L.length:ℝ)*B := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have ha := h a (by simp)
    have hL := ih (fun z hz => h z (by simp [hz]))
    simp only [List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    exact (norm_add_le _ _).trans (by linarith)

theorem microcoreTermSum_norm_bound {n : ℕ} (v θ : ℝ) (w : AngularSpace n → ℝ)
    (F : ℂ × (Fin (n+1) → ℂ) → ℂ) (s : ℂ) (x : AngularSpace n)
    (J j : ℕ) (hj : j ≤ J) (C D W : ℝ) (hC : 1 ≤ C) (hW : 0 ≤ W)
    (hF : AnalyticAt ℂ F (s,chartMap v θ s x))
    (hAjoint : ∀ i, AnalyticAt ℂ (fun t : ℂ × (Fin (n+1) → ℂ) => regularA t.1 (t.2 i))
      (s,chartMap v θ s x))
    (hFjet : JetBound (fun t => F (t,chartMap v θ s x)) s J D)
    (hA : ∀ i, JetBound (fun t => regularA t (chartMap v θ s x i)) s J C)
    (hw : ∀ l : List (Fin (n+1)), l.length ≤ j → ‖cutoffJet l w x‖ ≤ W) :
    ‖microcoreTermSum v θ w F j s x‖ ≤
      ‖chartJacobian v θ s x‖*((n+2:ℝ)^j*W*((2^J*C)^j*D)) := by
  let L := microcoreJetTerms F j
  have hT := microcoreJetTerms_parameter_budget F s (chartMap v θ s x) J j hj C D hC
    hF hAjoint hFjet hA
  have he : microcoreTermSum v θ w F j s x = chartJacobian v θ s x*
      (L.map (fun T => (cutoffJet T.cutoff w x:ℂ)*T.regularPart (s,chartMap v θ s x))).sum := by
    unfold microcoreTermSum
    rw [← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro T _
    unfold MicrocoreJetTerm.sourceValue chartPullback
    change (cutoffJet T.cutoff w x:ℂ)*(chartJacobian v θ s x*T.regularPart (s,chartMap v θ s x)) = _
    ring
  rw [he,norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hb := norm_list_sum_le_length_mul
    (L.map (fun T => (cutoffJet T.cutoff w x:ℂ)*T.regularPart (s,chartMap v θ s x)))
    (W*((2^J*C)^j*D)) (by
      intro z hz
      obtain ⟨T,hmem,rfl⟩ := List.mem_map.mp hz
      have ht := (hT T hmem).bound 0 (Nat.zero_le _)
      simp only [norm_iteratedFDeriv_zero] at ht
      rw [norm_mul,Complex.norm_real]
      exact mul_le_mul (hw T.cutoff (microcoreJetTerms_cutoff_length F j T hmem)) ht
        (norm_nonneg _) hW)
  have hlen : (L.length:ℝ)=(n+2:ℝ)^j := by
    dsimp [L]
    rw [microcoreJetTerms_length]
    push_cast
    ring
  rw [List.length_map,hlen] at hb
  nlinarith

end
end IsingBulk.Tail
