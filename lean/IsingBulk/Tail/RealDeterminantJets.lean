import IsingBulk.Tail.DeformedVandermondeJets
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace IsingBulk.Tail
noncomputable section
open scoped Topology ContDiff BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
set_option maxHeartbeats 1500000

theorem RealScaledJetBound.const_mul {f : E → ℂ} {x : E} {J : ℕ} {ρ C : ℝ} {a : ℤ}
    (h : RealScaledJetBound f x J ρ C a) (c : ℂ) :
    RealScaledJetBound (fun y => c*f y) x J ρ (‖c‖*C) a := by
  have hC := h.nonneg
  refine ⟨h.smooth.const_smul c,by positivity,?_⟩
  intro k hk
  change ‖iteratedFDeriv ℝ k (fun y => c • f y) x‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' (h.smooth.of_le (show (k:ℕ∞ω) ≤ ∞ by simp)),norm_smul]
  exact (mul_le_mul_of_nonneg_left (h.bound k hk) (norm_nonneg c)).trans_eq (by ring)

theorem RealScaledJetBound.const (x : E) (J : ℕ) (c : ℂ) :
    RealScaledJetBound (fun _ : E => c) x J 1 ‖c‖ 0 := by
  refine ⟨contDiffAt_const,norm_nonneg _,?_⟩
  intro k hk
  cases k with
  | zero => simp
  | succ k => simp [iteratedFDeriv_succ_const]

/-- Direct determinant expansion. The factorial cost cancels the exact source
normalization below; no estimate on an inverse matrix is required. -/
theorem real_determinant_uniform_jets {N : ℕ} (A : E → Matrix (Fin N) (Fin N) ℂ)
    (x : E) (J : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ i j, RealScaledJetBound (fun y => A y i j) x J 1 C 0) :
    RealScaledJetBound (fun y => (A y).det) x J 1
      ((N.factorial:ℝ)*(C^N*(max 1 (N:ℝ))^J)) 0 := by
  have hterm (σ : Equiv.Perm (Fin N)) :
      RealScaledJetBound (fun y => Equiv.Perm.sign σ • ∏ i, A y (σ i) i)
        x J 1 (C^N*(max 1 (N:ℝ))^J) 0 := by
    have hh := RealScaledJetBound.finset_prod Finset.univ (fun i _ => h (σ i) i) hC zero_lt_one
    simp only [Finset.card_univ,Fintype.card_fin,zero_mul] at hh
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with he | he
    · simpa only [he,one_smul] using hh
    · simpa [he] using hh.neg
  have hb := RealScaledJetBound.finset_sum Finset.univ (fun σ _ => hterm σ) (by positivity : 0 ≤ C^N*(max 1 (N:ℝ))^J)
  simpa only [Finset.card_univ,Fintype.card_perm,Fintype.card_fin,← Matrix.det_apply] using hb

theorem real_normalized_determinant_jets {N : ℕ} (A : E → Matrix (Fin N) (Fin N) ℂ)
    (x : E) (J : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ i j, RealScaledJetBound (fun y => A y i j) x J 1 C 0) :
    RealScaledJetBound (fun y => (N.factorial:ℂ)⁻¹*(A y).det) x J 1
      (C^N*(max 1 (N:ℝ))^J) 0 := by
  have hh := (real_determinant_uniform_jets A x J C hC h).const_mul ((N.factorial:ℂ)⁻¹)
  have hn : (N.factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero N
  simpa only [norm_inv,Complex.norm_natCast,← mul_assoc,inv_mul_cancel₀ hn,one_mul] using hh

end
end IsingBulk.Tail
