import IsingBulk.Tail.CompactRegularNumeratorJets
import IsingBulk.Tail.PeriodicGaussianPairs

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter
open scoped Topology ContDiff BigOperators
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Only the differentiated pairs pay a jet cost. The complete surviving
product remains as its original bound B, without division by pair factors. -/
theorem actual_compact_regular_numerator_deleted_jets (d : LocalBranchData)
    (f : SelectorFunctions) (hf : RegularSelector f) (hp1 : ∀ x, f.p x ≤ 1) {a b : ℝ}
    (hmargin : ∀ θ ∈ Icc a b, |1+Real.cos d.thetaB-Real.cos θ| < 1)
    (J : ℕ) : ∃ δ C : ℝ, 0 < δ ∧ 1 ≤ C ∧
      ∀ N : ℕ, 0 < N → ∀ eps τ lam : ℝ, 0 < eps → 0 ≤ τ → τ ≤ 1 →
      0 ≤ lam → lam ≤ 1 → ∀ s : ℂ, s ∈ dampingDomain (Real.exp (-d.c₀*eps)) →
      ‖s-radialParameter d.theta 0‖+d.c₀*eps+2*lam ≤ δ →
      ∀ θ : Fin N → ℝ, (∀ i, θ i ∈ Icc a b) → ∀ B : ℝ, 0 ≤ B →
      (∀ E ⊆ orderedIndexPairs (Finset.univ : Finset (Fin N)), E.card ≤ J →
        actualDeletedPairNorm f (Real.exp (-d.c₀*eps)) τ lam s E θ ≤ B) →
      RealScaledJetBound (fun q : ℂ × (Fin N → ℝ) =>
        compactRegularDensity f (Real.exp (-d.c₀*eps)) τ lam q.1 q.2)
        (s,θ) J 1 (2^J*C^(N+J)*(N:ℝ)^(5*J)*B) 0 := by
  obtain ⟨δA,A,hδA,hA,hpref⟩ := actual_compact_prefactor_jets d f hf hp1 hmargin J
  obtain ⟨δD,D,hδD,hD,hpair⟩ := actual_compact_complete_pair_uniform_jets d f hf hp1 hmargin J
  let C := A+D
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hAC : A ≤ C := by dsimp [C]; linarith
  have hDC : D ≤ C := by dsimp [C]; linarith
  refine ⟨min δA δD,C,lt_min hδA hδD,hC,?_⟩
  intro N hN eps τ lam heps hτ hτ1 hlam hlam1 s hs hsmall θ hθ B hB hremain
  let r := Real.exp (-d.c₀*eps)
  let S := orderedIndexPairs (Finset.univ : Finset (Fin N))
  let F := fun (ij : Fin N × Fin N) (q : ℂ × (Fin N → ℝ)) =>
    canceledPair (deformedPoint f r τ lam q.2 ij.1) (deformedPoint f r τ lam q.2 ij.2)
      (globalRoot q.1 (deformedPoint f r τ lam q.2 ij.1)) (globalRoot q.1 (deformedPoint f r τ lam q.2 ij.2))
  have hpre := (hpref N hN eps τ lam heps hτ hτ1 hlam hlam1 s hs
    (hsmall.trans (min_le_left _ _)) θ hθ).mono zero_lt_one le_rfl
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (zero_le_one.trans hA) hAC N) (by positivity))
  have hprod := compact_complete_product_deleted_jets F S (s,θ) J C B hC hB
    (fun ij _ => (hpair N hN eps τ lam heps hτ hτ1 hlam hlam1 s hs
      (hsmall.trans (min_le_right _ _)) θ hθ ij.1 ij.2).mono zero_lt_one le_rfl hDC)
    hremain
  have hcS : S.card ≤ N^2 := by
    simpa only [Fintype.card_prod,Fintype.card_fin,pow_two] using S.card_le_univ
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hm : max 1 (S.card:ℝ) ≤ (N:ℝ)^2 := max_le (one_le_pow₀ hN1) (by exact_mod_cast hcS)
  have hprod' := hprod.mono zero_lt_one le_rfl
    (show (max 1 (S.card:ℝ))^J*C^J*B ≤ (N:ℝ)^(2*J)*C^J*B from by rw [pow_mul]; gcongr)
  have hh := hpre.mul hprod' zero_lt_one
  simp only [zero_add] at hh
  have he : 2^J*(C^N*(N:ℝ)^(3*J))*((N:ℝ)^(2*J)*C^J*B)=2^J*C^(N+J)*(N:ℝ)^(5*J)*B := by
    rw [show 5*J=3*J+2*J by omega]
    simp only [pow_add]
    ring
  rw [he] at hh
  apply hh.congr
  exact Eventually.of_forall (fun q => by
    dsimp only
    rw [compactRegularDensity_prefactor,canceledPairProduct_indexed])

theorem compact_gaussian_cost_absorption {N J : ℕ} (hN : 0 < N) {C B : ℝ}
    (hC : 1 ≤ C) (hB : 0 ≤ B) :
    2^J*C^(N+J)*B^N ≤ (2^J*C^(J+1)*max 1 B)^N := by
  have hbase : 1 ≤ (2:ℝ)^J*C^J := one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ (by norm_num)) (one_le_pow₀ hC)
  have hh : (2:ℝ)^J*C^J ≤ ((2:ℝ)^J*C^J)^N := le_self_pow₀ hbase (by omega : N ≠ 0)
  calc
    _ = (2^J*C^J)*(C*B)^N := by rw [pow_add,mul_pow]; ring
    _ ≤ ((2:ℝ)^J*C^J)^N*(C*max 1 B)^N := by gcongr; exact le_max_right 1 B
    _ = _ := by rw [← mul_pow,pow_succ]; congr 1; ring

end
end IsingBulk.Tail
