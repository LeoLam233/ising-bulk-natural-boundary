import IsingBulk.Tail.AllBranchExteriorAnisotropic

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets
open scoped BigOperators

theorem allBranchExterior_vandermonde_homogeneous {N : ℕ} (c : ℂ) (φ : Fin N → ℂ) :
    microcoreVandermondeSquared (fun i => c*φ i)=c^(N*(N-1))*microcoreVandermondeSquared φ := by
  rw [microcore_vandermonde_indexed,microcore_vandermonde_indexed]
  simp_rw [← mul_sub,mul_pow]
  rw [Finset.prod_mul_distrib,Finset.prod_const,← pow_mul,orderedIndexPairs_card,
    Finset.card_univ,Fintype.card_fin]
  have hc : 2*N.choose 2=N*(N-1) := by
    rw [Nat.choose_two_right,Nat.mul_div_cancel' (Nat.even_mul_pred_self N).two_dvd]
  rw [hc]

theorem allBranchExterior_scaled_unfactored {N : ℕ} (R : ℝ)
    (A : ℂ × (Fin N → ℂ) → ℂ) (z : ℂ × (Fin N → ℂ)) :
    unfactoredNumerator A (allBranchPhaseScale R z)=
      (R:ℂ)^(N*(N-1))*microcoreVandermondeSquared z.2*A (allBranchPhaseScale R z) := by
  rw [allBranchExterior_unfactored_eq,allBranchPhaseScale_apply,allBranchExterior_vandermonde_homogeneous]

theorem allBranchExterior_unit_vandermonde_budget {N : ℕ} (z : ℂ × (Fin N → ℂ))
    (J : ℕ) (hφ : ∀ p q, ‖z.2 p-z.2 q‖ ≤ 2) :
    JetBound (fun t : ℂ × (Fin N → ℂ) => microcoreVandermondeSquared t.2) z J
      ((8:ℝ)^(N.choose 2)*((N.choose 2:ℝ)+1)^J) := by
  have ha : AnalyticAt ℂ (@microcoreVandermondeSquared N) z.2 := by
    unfold microcoreVandermondeSquared
    apply Finset.analyticAt_fun_prod
    intro i _
    apply Finset.analyticAt_fun_prod
    intro j _
    exact (((ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ).analyticAt z.2).sub
      ((ContinuousLinearMap.proj j : (Fin N → ℂ) →L[ℂ] ℂ).analyticAt z.2)).pow 2
  refine ⟨AnalyticAt.comp (g := @microcoreVandermondeSquared N) (f := Prod.snd) ha analyticAt_snd,
    by positivity,?_⟩
  intro k hk
  have hL : ‖ContinuousLinearMap.snd ℂ ℂ (Fin N → ℂ)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro y
    change ‖y.2‖ ≤ 1*max ‖y.1‖ ‖y.2‖
    simpa only [one_mul] using le_max_right ‖y.1‖ ‖y.2‖
  have hh := analytic_linear_comp_jet_bound (@microcoreVandermondeSquared N)
    (ContinuousLinearMap.snd ℂ ℂ (Fin N → ℂ)) z k ha hL
  have hv := allBranchExterior_vandermonde_jets z.2 1 (by norm_num)
    (by simpa using hφ) k
  have hpow : (N.choose 2:ℝ)^k ≤ ((N.choose 2:ℝ)+1)^J := by
    apply (pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith : (N.choose 2:ℝ) ≤ (N.choose 2:ℝ)+1) k).trans
    exact pow_le_pow_right₀ (by have := Nat.cast_nonneg (N.choose 2) (α := ℝ); linarith) hk
  simp only [one_zpow,mul_one] at hv
  have hb := hh.trans (hv.trans (mul_le_mul_of_nonneg_left hpow
    (by positivity : 0 ≤ (8:ℝ)^(N.choose 2))))
  convert! hb using 1

end
end IsingBulk.Tail
