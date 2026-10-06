import IsingBulk.Tail.AllBranchExteriorWeightedPole
import IsingBulk.Tail.AllBranchExteriorCoefficientBounds
import IsingBulk.Tail.AllBranchExteriorNearNumerator
import IsingBulk.Tail.MicrocorePointwiseBudget

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets IsingBulk.Lie

theorem allBranchExterior_sourceTerm_norm {n : ℕ} (T : SourceJetTerm (n+1))
    (p q : Fin (n+1)) (v θ : ℝ) (w : AngularSpace n → ℝ)
    (Q : ℂ × (Fin (n+1) → ℂ) → ℂ) (s : ℂ) (u : AngularSpace n)
    (W A B : ℝ) (hW : 0 ≤ W) (hA : 0 ≤ A)
    (hw : ‖cutoffJet T.cutoff w u‖/
      ‖selectedDifferenceCLM p q (s,chartMap v θ s u)‖^T.pole ≤ W)
    (hreg : ‖T.regularPart (s,chartMap v θ s u)‖ ≤ A)
    (hnum : ‖numeratorJet T.numerator Q (s,chartMap v θ s u)‖ ≤ B) :
    ‖T.sourceValue p q v θ w Q s u‖ ≤
      W*A*B*‖chartJacobian v θ s u‖/‖regularKernel s (chartMap v θ s u)‖ := by
  rw [T.sourceValue_eq]
  unfold SourceJetTerm.value SourceJetTerm.density SourceJetTerm.coefficient
  simp only [norm_mul,norm_div,norm_pow,Complex.norm_real]
  calc
    _ = ((‖cutoffJet T.cutoff w u‖/‖selectedDifferenceCLM p q (s,chartMap v θ s u)‖^T.pole)*
      ‖T.regularPart (s,chartMap v θ s u)‖*
      ‖numeratorJet T.numerator Q (s,chartMap v θ s u)‖)*
      ‖chartJacobian v θ s u‖/‖regularKernel s (chartMap v θ s u)‖ := by ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (norm_nonneg _)
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact mul_le_mul (mul_le_mul hw hreg (norm_nonneg _) hW) hnum (norm_nonneg _) (mul_nonneg hW hA)

/-- The complete generated list is bounded before taking the actual angular
integral. Its length is the literal six-action recurrence count. -/
theorem allBranchExterior_source_sum_norm {n : ℕ} (p q : Fin (n+1)) (j : ℕ)
    (v θ : ℝ) (w : AngularSpace n → ℝ) (Q : ℂ × (Fin (n+1) → ℂ) → ℂ)
    (s : ℂ) (u : AngularSpace n) (B : ℝ)
    (hb : ∀ T ∈ sourceJetTerms p q j, ‖T.sourceValue p q v θ w Q s u‖ ≤ B) :
    ‖((sourceJetTerms p q j).map (fun T => T.sourceValue p q v θ w Q s u)).sum‖ ≤
      (3+3*(n+1):ℝ)^j*B := by
  have hh := norm_list_sum_le_length_mul
    ((sourceJetTerms p q j).map (fun T => T.sourceValue p q v θ w Q s u)) B (by
      intro x hx
      obtain ⟨T,hT,rfl⟩ := List.mem_map.mp hx
      exact hb T hT)
  simpa only [List.length_map,sourceJetTerms_length,Nat.cast_pow,Nat.cast_add,Nat.cast_mul,
    Nat.cast_ofNat,Nat.cast_one] using hh

end
end IsingBulk.Tail
