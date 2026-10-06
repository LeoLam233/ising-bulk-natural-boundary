import IsingBulk.Tail.CompactRegularScalarJets
import IsingBulk.Tail.DeformedVandermondeJets

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter
open scoped Topology ContDiff BigOperators
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem compact_globalRoot_eventually_selected {N : ℕ} (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ lam : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam)
    {p : ℂ × (Fin N → ℝ)} (hp : p ∈ compactSourceDomain N r) :
    ∀ᶠ q in 𝓝 p, ∀ i, globalRoot q.1 (deformedPoint f r τ lam q.2 i)=
      selectedContinuedRoot q.1 (deformedPoint f r τ lam q.2 i) := by
  filter_upwards [(compactSourceDomain_isOpen N r).mem_nhds hp] with q hq i
  exact (continuedRoot_eq_interiorRoot
    (deformed_sourceW_upper_on_damping hN f hf hr hr1 hτ hlam hq.1 q.2 i)).symm

theorem canceledPairProduct_indexed {N : ℕ} (z y : Fin N → ℂ) :
    canceledPairProduct z y = ∏ p ∈ orderedIndexPairs (Finset.univ : Finset (Fin N)),
      canceledPair (y p.1) (y p.2) (z p.1) (z p.2) := by
  simp only [canceledPairProduct,orderedIndexPairs,Finset.prod_filter,Finset.prod_product]

theorem actual_compact_pair_product_collision_jets (d : LocalBranchData)
    (f : SelectorFunctions) (hf : RegularSelector f) (hp1 : ∀ x, f.p x ≤ 1) {a b : ℝ}
    (hmargin : ∀ θ ∈ Icc a b, |1+Real.cos d.thetaB-Real.cos θ| < 1)
    (J : ℕ) : ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ∀ N : ℕ, 0 < N → ∀ eps τ lam : ℝ, 0 < eps → 0 ≤ τ → τ ≤ 1 →
      0 ≤ lam → lam ≤ 1 → ∀ s : ℂ, s ∈ dampingDomain (Real.exp (-d.c₀*eps)) →
      ‖s-radialParameter d.theta 0‖+d.c₀*eps+2*lam ≤ δ →
      ∀ θ : Fin N → ℝ, (∀ i, θ i ∈ Icc a b) →
      ∀ P : Finset (Fin N × Fin N), ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      (∀ ij ∈ P, |θ ij.1-θ ij.2| ≤ ρ) →
      RealScaledJetBound (fun q : ℂ × (Fin N → ℝ) =>
        let y := deformedPoint f (Real.exp (-d.c₀*eps)) τ lam q.2
        ∏ ij ∈ P, canceledPair (y ij.1) (y ij.2) (globalRoot q.1 (y ij.1)) (globalRoot q.1 (y ij.2)))
        (s,θ) J ρ (C^P.card*(max 1 (P.card:ℝ))^J) (2*(P.card:ℤ)) := by
  obtain ⟨δ,B,hδ,hB,hscalar⟩ := actual_compact_regular_scalar_jets d f hf hp1 hmargin J
  obtain ⟨A,hA,hdiff⟩ := deformedPoint_difference_scaled_jets f hf J
  refine ⟨δ,2^J*(A^2*2^J)*B,hδ,by positivity,?_⟩
  intro N hN eps τ lam heps hτ hτ1 hlam hlam1 s hs hsmall θ hθ P ρ hρ hρ1 hgap
  let r := Real.exp (-d.c₀*eps)
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [d.c₀_pos])
  have hroot := compact_globalRoot_eventually_selected hN f hf hr hr1 hτ hlam
    (p := (s,θ)) ⟨hs,mem_univ _⟩
  apply RealScaledJetBound.finset_prod P _ (by positivity) hρ
  intro ij hij
  have hv := (hdiff N hN r τ lam hr.le hr1.le hτ hτ1 hlam hlam1 ij.1 ij.2 (s,θ)
    ρ hρ hρ1 (hgap ij hij)).pow hρ 2 (by norm_num)
  have hq := (hscalar N hN eps τ lam heps.le hτ hτ1 hlam hlam1 s hsmall θ
    ij.1 ij.2 (hθ _) (hθ _) (Sum.inl false)).rescale_zero hρ hρ1
  have hh := hv.mul hq hρ
  simp only [Nat.cast_ofNat,one_mul,add_zero] at hh
  apply hh.congr
  filter_upwards [hroot] with q hq
  rw [hq ij.1,hq ij.2]
  exact mixedCompactPair_factorization
    (q.1,deformedPoint f r τ lam q.2 ij.1,deformedPoint f r τ lam q.2 ij.2)

theorem actual_compact_complete_pair_uniform_jets (d : LocalBranchData)
    (f : SelectorFunctions) (hf : RegularSelector f) (hp1 : ∀ x, f.p x ≤ 1) {a b : ℝ}
    (hmargin : ∀ θ ∈ Icc a b, |1+Real.cos d.thetaB-Real.cos θ| < 1)
    (J : ℕ) : ∃ δ C : ℝ, 0 < δ ∧ 1 ≤ C ∧
      ∀ N : ℕ, 0 < N → ∀ eps τ lam : ℝ, 0 < eps → 0 ≤ τ → τ ≤ 1 →
      0 ≤ lam → lam ≤ 1 → ∀ s : ℂ, s ∈ dampingDomain (Real.exp (-d.c₀*eps)) →
      ‖s-radialParameter d.theta 0‖+d.c₀*eps+2*lam ≤ δ →
      ∀ θ : Fin N → ℝ, (∀ i, θ i ∈ Icc a b) → ∀ i j,
      RealScaledJetBound (fun q : ℂ × (Fin N → ℝ) =>
        let y := deformedPoint f (Real.exp (-d.c₀*eps)) τ lam q.2
        canceledPair (y i) (y j) (globalRoot q.1 (y i)) (globalRoot q.1 (y j))) (s,θ) J 1 C 0 := by
  obtain ⟨δ,C,hδ,hC,hscalar⟩ := actual_compact_regular_scalar_jets d f hf hp1 hmargin J
  refine ⟨δ,C,hδ,hC,?_⟩
  intro N hN eps τ lam heps hτ hτ1 hlam hlam1 s hs hsmall θ hθ i j
  have hr1 : Real.exp (-d.c₀*eps) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [d.c₀_pos])
  apply (hscalar N hN eps τ lam heps.le hτ hτ1 hlam hlam1 s hsmall θ i j
    (hθ _) (hθ _) (Sum.inl true)).congr
  filter_upwards [compact_globalRoot_eventually_selected hN f hf (Real.exp_pos _) hr1 hτ hlam
    (p := (s,θ)) ⟨hs,mem_univ _⟩] with q hq
  dsimp only
  rw [hq i,hq j]
  rfl

/-- The already bounded surviving factors are retained intact in the angular
Leibniz expansion. This estimate is also valid when any such factor is zero. -/
theorem compact_complete_product_deleted_jets {N : ℕ}
    (f : (Fin N × Fin N) → (ℂ × (Fin N → ℝ)) → ℂ)
    (P : Finset (Fin N × Fin N)) (x : ℂ × (Fin N → ℝ)) (J : ℕ) (C B : ℝ)
    (hC : 1 ≤ C) (hB : 0 ≤ B) (hjet : ∀ i ∈ P, RealScaledJetBound (f i) x J 1 C 0)
    (hremain : ∀ E ⊆ P, E.card ≤ J → ∏ i ∈ P \ E, ‖f i x‖ ≤ B) :
    RealScaledJetBound (fun y => ∏ i ∈ P, f i y) x J 1
      ((max 1 (P.card:ℝ))^J*C^J*B) 0 := by
  refine ⟨contDiffAt_prod (fun i hi => (hjet i hi).smooth),by positivity,?_⟩
  intro k hk
  simp only [one_zpow,mul_one]
  have hh := smooth_product_changed_factors_bound P f x J C B hC hB
    (fun i hi => (hjet i hi).smooth)
    (fun i hi k _ hk => by simpa only [one_zpow,mul_one] using (hjet i hi).bound k hk)
    hremain k hk
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ hB
  apply mul_le_mul _ (pow_le_pow_right₀ hC hk) (by positivity) (by positivity)
  exact (pow_le_pow_left₀ (by positivity) (le_max_right 1 (P.card:ℝ)) k).trans
    (pow_le_pow_right₀ (le_max_left 1 (P.card:ℝ)) hk)

end
end IsingBulk.Tail
