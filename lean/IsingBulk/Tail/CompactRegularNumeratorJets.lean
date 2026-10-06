import IsingBulk.Tail.CompactRegularPrefactorJets

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter
open scoped Topology ContDiff BigOperators
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem compact_pair_product_cost {N J : ℕ} (hN : 0 < N) (P : Finset (Fin N × Fin N))
    {B C : ℝ} (hB : 0 ≤ B) (hC : 1 ≤ C) (hBC : B ≤ C) :
    B^P.card*(max 1 (P.card:ℝ))^J ≤ C^(N^2)*(N:ℝ)^(2*J) := by
  have hc : P.card ≤ N^2 := by
    simpa only [Fintype.card_prod,Fintype.card_fin,pow_two] using P.card_le_univ
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hnc : (P.card:ℝ) ≤ (N:ℝ)^2 := by exact_mod_cast hc
  have hm : max 1 (P.card:ℝ) ≤ (N:ℝ)^2 := max_le (one_le_pow₀ hN1) hnc
  have hpow := (pow_le_pow_left₀ hB hBC P.card).trans (pow_le_pow_right₀ hC hc)
  rw [pow_mul]
  exact mul_le_mul hpow (pow_le_pow_left₀ (by positivity) hm J) (by positivity) (by positivity)

def compactNearNumeratorCost (C : ℝ) (N J : ℕ) : ℝ :=
  2^(2*J)*C^(2*N^2+N)*(N:ℝ)^(7*J)

/-- All literal regular factors, including the angular Jacobian and source
normalization. Any subset of pairs may carry the collision power, allowing
the named Stokes coordinate to be excluded from that subset. -/
theorem actual_compact_regular_numerator_collision_jets (d : LocalBranchData)
    (f : SelectorFunctions) (hf : RegularSelector f) (hp1 : ∀ x, f.p x ≤ 1) {a b : ℝ}
    (hmargin : ∀ θ ∈ Icc a b, |1+Real.cos d.thetaB-Real.cos θ| < 1)
    (J : ℕ) : ∃ δ C : ℝ, 0 < δ ∧ 1 ≤ C ∧
      ∀ N : ℕ, 0 < N → ∀ eps τ lam : ℝ, 0 < eps → 0 ≤ τ → τ ≤ 1 →
      0 ≤ lam → lam ≤ 1 → ∀ s : ℂ, s ∈ dampingDomain (Real.exp (-d.c₀*eps)) →
      ‖s-radialParameter d.theta 0‖+d.c₀*eps+2*lam ≤ δ →
      ∀ θ : Fin N → ℝ, (∀ i, θ i ∈ Icc a b) →
      ∀ P : Finset (Fin N × Fin N), P ⊆ orderedIndexPairs Finset.univ →
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → (∀ ij ∈ P, |θ ij.1-θ ij.2| ≤ ρ) →
      RealScaledJetBound (fun q : ℂ × (Fin N → ℝ) =>
        compactRegularDensity f (Real.exp (-d.c₀*eps)) τ lam q.1 q.2)
        (s,θ) J ρ (compactNearNumeratorCost C N J) (2*(P.card:ℤ)) := by
  obtain ⟨δA,A,hδA,hA,hpref⟩ := actual_compact_prefactor_jets d f hf hp1 hmargin J
  obtain ⟨δB,B,hδB,hB,hcollision⟩ := actual_compact_pair_product_collision_jets d f hf hp1 hmargin J
  obtain ⟨δD,D,hδD,hD,hpair⟩ := actual_compact_complete_pair_uniform_jets d f hf hp1 hmargin J
  let C := A+B+D
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hAC : A ≤ C := by dsimp [C]; linarith
  have hBC : B ≤ C := by dsimp [C]; linarith
  have hDC : D ≤ C := by dsimp [C]; linarith
  refine ⟨min δA (min δB δD),C,lt_min hδA (lt_min hδB hδD),hC,?_⟩
  intro N hN eps τ lam heps hτ hτ1 hlam hlam1 s hs hsmall θ hθ P hP ρ hρ hρ1 hgap
  let r := Real.exp (-d.c₀*eps)
  let S := orderedIndexPairs (Finset.univ : Finset (Fin N))
  let F := fun (ij : Fin N × Fin N) (q : ℂ × (Fin N → ℝ)) =>
    canceledPair (deformedPoint f r τ lam q.2 ij.1) (deformedPoint f r τ lam q.2 ij.2)
      (globalRoot q.1 (deformedPoint f r τ lam q.2 ij.1)) (globalRoot q.1 (deformedPoint f r τ lam q.2 ij.2))
  have hpre := hpref N hN eps τ lam heps hτ hτ1 hlam hlam1 s hs
    (hsmall.trans (min_le_left _ _)) θ hθ
  have hpre' := (hpre.mono zero_lt_one le_rfl
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (zero_le_one.trans hA) hAC N) (by positivity))).rescale_zero hρ hρ1
  have hcol := hcollision N hN eps τ lam heps hτ hτ1 hlam hlam1 s hs
    (hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))) θ hθ P ρ hρ hρ1 hgap
  have hcol' := hcol.mono hρ le_rfl (compact_pair_product_cost (J := J) hN P hB.le hC hBC)
  have hrest := RealScaledJetBound.finset_prod (S \ P)
    (fun ij _ => hpair N hN eps τ lam heps hτ hτ1 hlam hlam1 s hs
      (hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))) θ hθ ij.1 ij.2)
    (zero_le_one.trans hD) zero_lt_one
  simp only [zero_mul] at hrest
  have hrest' := (hrest.mono zero_lt_one le_rfl
    (compact_pair_product_cost (J := J) hN (S \ P) (zero_le_one.trans hD) hC hDC)).rescale_zero hρ hρ1
  have hprod : RealScaledJetBound (fun q => ∏ ij ∈ S, F ij q) (s,θ) J ρ
      (2^J*(C^(N^2)*(N:ℝ)^(2*J))*(C^(N^2)*(N:ℝ)^(2*J))) (2*(P.card:ℤ)) := by
    apply (hcol'.mul hrest' hρ).congr
    exact Eventually.of_forall (fun q => by
      change (∏ ij ∈ S,F ij q)=(∏ ij ∈ P,F ij q)*(∏ ij ∈ S \ P,F ij q)
      rw [mul_comm,Finset.prod_sdiff hP])
  have hh := hpre'.mul hprod hρ
  simp only [zero_add] at hh
  have he : 2^J*(C^N*(N:ℝ)^(3*J))*
      (2^J*(C^(N^2)*(N:ℝ)^(2*J))*(C^(N^2)*(N:ℝ)^(2*J)))=compactNearNumeratorCost C N J := by
    unfold compactNearNumeratorCost
    rw [show 2*J=J+J by omega,show 7*J=3*J+(J+J)+(J+J) by omega,
      show 2*N^2+N=N+N^2+N^2 by omega]
    simp only [pow_add]
    ring
  rw [he] at hh
  apply hh.congr
  exact Eventually.of_forall (fun q => by
    dsimp only
    rw [compactRegularDensity_prefactor,canceledPairProduct_indexed])

end
end IsingBulk.Tail
