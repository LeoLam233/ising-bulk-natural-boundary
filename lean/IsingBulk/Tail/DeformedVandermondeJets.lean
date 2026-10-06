import IsingBulk.Tail.DeformedDifferenceJets
import IsingBulk.Tail.IndexedPairCounting

/-! The actual coupled deformation preserves the full collision degree of a
finite Vandermonde product. The constants are fixed before particle number. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First Set
open scoped Topology ContDiff BigOperators
set_option maxHeartbeats 1500000

theorem RealScaledJetBound.finset_prod {E ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [DecidableEq ι] (S : Finset ι) {f : ι → E → ℂ}
    {x : E} {J : ℕ} {ρ C : ℝ} {a : ℤ}
    (h : ∀ i ∈ S, RealScaledJetBound (f i) x J ρ C a) (hC : 0 ≤ C) (hρ : 0 < ρ) :
    RealScaledJetBound (fun y => ∏ i ∈ S, f i y) x J ρ
      (C^S.card*(max 1 (S.card:ℝ))^J) (a*(S.card:ℤ)) := by
  refine ⟨contDiffAt_prod (fun i hi => (h i hi).smooth),by positivity,?_⟩
  intro k hk
  have hb := smooth_finset_product_scaled_jets S f x J C ρ a hC hρ
    (fun i hi => (h i hi).smooth) (fun i hi => (h i hi).bound) k hk
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (zpow_nonneg hρ.le _)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (pow_le_pow_left₀ (by positivity) (le_max_right 1 (S.card:ℝ)) k).trans
    (pow_le_pow_right₀ (le_max_left 1 (S.card:ℝ)) hk)

theorem deformed_vandermonde_scaled_jets (f : SelectorFunctions) (hf : RegularSelector f)
    (J : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N → ∀ r τ lam : ℝ,
      0 ≤ r → r ≤ 1 → 0 ≤ τ → τ ≤ 1 → 0 ≤ lam → lam ≤ 1 →
      ∀ P : Finset (Fin N × Fin N), ∀ p : ℂ × (Fin N → ℝ), ∀ ρ : ℝ,
      0 < ρ → ρ ≤ 1 → (∀ ij ∈ P, |p.2 ij.1-p.2 ij.2| ≤ ρ) →
      RealScaledJetBound (fun q : ℂ × (Fin N → ℝ) =>
        ∏ ij ∈ P, (deformedPoint f r τ lam q.2 ij.1-deformedPoint f r τ lam q.2 ij.2)^2)
        p J ρ (C^P.card*(max 1 (P.card:ℝ))^J) (2*(P.card:ℤ)) := by
  obtain ⟨A,hA,hj⟩ := deformedPoint_difference_scaled_jets f hf J
  refine ⟨A^2*(2:ℝ)^J,by positivity,?_⟩
  intro N hN r τ lam hr hr1 hτ hτ1 hlam hlam1 P p ρ hρ hρ1 hgap
  apply RealScaledJetBound.finset_prod P _ (by positivity) hρ
  intro ij hij
  simpa only [Nat.cast_ofNat,one_mul] using
    (hj N hN r τ lam hr hr1 hτ hτ1 hlam hlam1 ij.1 ij.2 p ρ hρ hρ1 (hgap ij hij)).pow
      hρ 2 (by norm_num)

end
end IsingBulk.Tail
