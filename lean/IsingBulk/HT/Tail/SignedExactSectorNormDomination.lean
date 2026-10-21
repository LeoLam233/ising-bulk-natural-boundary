import IsingBulk.HT.Tail.SignedSectorNorms
import IsingBulk.HT.Tail.SignedSectorCurrentExclusion
import IsingBulk.HT.Tail.SignedHighKSBound

/-! Exact signed K/S domination by the actual exhaustive finite sector
partition. The constructed current exclusion is uniform in every parameter
and derivative order; no sector norm estimate is assumed at the endpoint. -/
namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour MeasureTheory Set
open scoped BigOperators Topology Classical

/-- The existing exact source decompositions give the finite norm bound as
soon as the all-branch small-current term is known to vanish. -/
theorem signed_originalKSNorm_le_sectors_of_current_none_zero (σ : ℂ) (hσ : ‖σ‖ = 1) (N : ℕ) (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r tau cut : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (htau : 0 ≤ tau) (hcut : cut ∈ Icc (0:ℝ) 1)
    (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner) (j : ℕ) (s : ℂ)
    (hs : s ∈ dampingDomain r)
    (hzero : ∀ q : Fin N,
      signedSmallCurrentSectorIntegral σ N f r tau cut q b outer inner ho hi none j s = 0) :
    signedOriginalKSNorm σ N f r tau j s cut ≤
      ‖iteratedDeriv j (signedOriginalSectorIntegral σ N f r tau b outer inner ho hi none) s‖ +
      signedMixedLeftSectorNorm σ N f r tau b outer inner ho hi j s cut +
      signedRightCompactSectorNorm σ N f r tau b outer inner ho hi j s cut := by
  classical
  have hK : ‖iteratedDeriv j (signedOriginalLowerIntegral σ N f r tau) s‖ ≤
      ‖iteratedDeriv j (signedOriginalSectorIntegral σ N f r tau b outer inner ho hi none) s‖ +
      (signedOriginalMixedSectorNorm σ N f r tau b outer inner ho hi j s +
        signedOriginalLeftCompactSectorNorm σ N f r tau b outer inner ho hi j s +
        signedOriginalRightCompactSectorNorm σ N f r tau b outer inner ho hi j s) := by
    rw [signed_originalLower_sector_derivative σ hσ N hN f hf hr hr1 htau b outer inner ho hi s hs j]
    calc
      _ ≤ ∑ label, ‖iteratedDeriv j
          (signedOriginalSectorIntegral σ N f r tau b outer inner ho hi label) s‖ :=
        norm_sum_le _ _
      _ = ‖iteratedDeriv j (signedOriginalSectorIntegral σ N f r tau b outer inner ho hi none) s‖ +
          ∑ qa, ‖iteratedDeriv j
            (signedOriginalSectorIntegral σ N f r tau b outer inner ho hi (some qa)) s‖ := by
        rw [Fintype.sum_option]
      _ ≤ _ := by
        apply add_le_add le_rfl
        simpa only [signedOriginalMixedSectorNorm, signedOriginalLeftCompactSectorNorm,
          signedOriginalRightCompactSectorNorm] using
          nested_sector_norm_le_categories (fun qa => iteratedDeriv j
            (signedOriginalSectorIntegral σ N f r tau b outer inner ho hi (some qa)) s)
  have hS : ‖∫ lam in 0..cut, signedDifferentiatedCurrentSlice σ N f r tau lam j s‖ ≤
      signedIntegratedMixedSectorNorm σ N f r tau b outer inner ho hi j s cut +
        signedIntegratedLeftCompactSectorNorm σ N f r tau b outer inner ho hi j s cut +
        signedIntegratedRightCompactSectorNorm σ N f r tau b outer inner ho hi j s cut := by
    rw [signed_small_current_sector_decomposition σ hσ N hN f hf hr hr1 htau hcut
      b outer inner ho hi j hs]
    calc
      _ ≤ ∑ q : Fin N, ‖∑ label,
          signedSmallCurrentSectorIntegral σ N f r tau cut q b outer inner ho hi label j s‖ :=
        norm_sum_le _ _
      _ ≤ ∑ q : Fin N, ∑ label,
          ‖signedSmallCurrentSectorIntegral σ N f r tau cut q b outer inner ho hi label j s‖ := by
        apply Finset.sum_le_sum
        intro q _
        exact norm_sum_le _ _
      _ = ∑ q : Fin N, ∑ qa : Fin N × (Fin N → Fin 3),
          ‖signedSmallCurrentSectorIntegral σ N f r tau cut q b outer inner ho hi (some qa) j s‖ := by
        apply Finset.sum_congr rfl
        intro q _
        rw [Fintype.sum_option, hzero q, norm_zero, zero_add]
      _ ≤ ∑ q : Fin N,
          ((∑ qa : Fin N × (Fin N → Fin 3), if ∃ i, qa.2 i=2 then
            ‖signedSmallCurrentSectorIntegral σ N f r tau cut q b outer inner ho hi (some qa) j s‖ else 0) +
          (∑ qa : Fin N × (Fin N → Fin 3), if leftCompactAssignment qa.2 then
            ‖signedSmallCurrentSectorIntegral σ N f r tau cut q b outer inner ho hi (some qa) j s‖ else 0) +
          (∑ qa : Fin N × (Fin N → Fin 3), if ∀ i, qa.2 i=1 then
            ‖signedSmallCurrentSectorIntegral σ N f r tau cut q b outer inner ho hi (some qa) j s‖ else 0)) := by
        apply Finset.sum_le_sum
        intro q _
        exact nested_sector_norm_le_categories (fun qa =>
          signedSmallCurrentSectorIntegral σ N f r tau cut q b outer inner ho hi (some qa) j s)
      _ = _ := by
        simp only [Finset.sum_add_distrib, signedSmallCurrentSectorIntegral,
          signedIntegratedMixedSectorNorm, signedIntegratedLeftCompactSectorNorm,
          signedIntegratedRightCompactSectorNorm]
  calc
    signedOriginalKSNorm σ N f r tau j s cut =
        ‖iteratedDeriv j (signedOriginalLowerIntegral σ N f r tau) s‖ +
        ‖∫ lam in 0..cut, signedDifferentiatedCurrentSlice σ N f r tau lam j s‖ := rfl
    _ ≤ (‖iteratedDeriv j (signedOriginalSectorIntegral σ N f r tau b outer inner ho hi none) s‖ +
        (signedOriginalMixedSectorNorm σ N f r tau b outer inner ho hi j s +
          signedOriginalLeftCompactSectorNorm σ N f r tau b outer inner ho hi j s +
          signedOriginalRightCompactSectorNorm σ N f r tau b outer inner ho hi j s)) +
        (signedIntegratedMixedSectorNorm σ N f r tau b outer inner ho hi j s cut +
          signedIntegratedLeftCompactSectorNorm σ N f r tau b outer inner ho hi j s cut +
          signedIntegratedRightCompactSectorNorm σ N f r tau b outer inner ho hi j s cut) :=
      add_le_add hK hS
    _ = _ := by
      unfold signedMixedLeftSectorNorm signedRightCompactSectorNorm
      ring

/-- Derivative-level current exclusion is sufficient for the exact finite
source domination. It is supplied by the constructed selector below. -/
theorem signed_originalKSNorm_le_sectors (σ : ℂ) (hσ : ‖σ‖ = 1) (N : ℕ) (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r tau cut : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (htau : 0 ≤ tau) (hcut : cut ∈ Icc (0:ℝ) 1)
    (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner) (j : ℕ) (s : ℂ)
    (hs : s ∈ dampingDomain r)
    (hzero : ∀ (q : Fin N) (lam : ℝ), iteratedDeriv j
      (signedCurrentSectorIntegral σ N f r tau lam q b outer inner ho hi none) s = 0) :
    signedOriginalKSNorm σ N f r tau j s cut ≤
      ‖iteratedDeriv j (signedOriginalSectorIntegral σ N f r tau b outer inner ho hi none) s‖ +
      signedMixedLeftSectorNorm σ N f r tau b outer inner ho hi j s cut +
      signedRightCompactSectorNorm σ N f r tau b outer inner ho hi j s cut := by
  apply signed_originalKSNorm_le_sectors_of_current_none_zero σ hσ N hN f hf hr hr1 htau hcut
    b outer inner ho hi j s hs
  intro q
  simp only [signedSmallCurrentSectorIntegral, hzero q, intervalIntegral.integral_zero]

/-- The constructed source satisfies the domination without any additional
analytic or norm estimate premise. The outer cap is chosen before the source
radius, homotopy parameters, particle number, and derivative order. -/
theorem signed_constructed_originalKSNorm_le_sectors (σ : ℂ) (hσ : ‖σ‖ = 1) {b eta : ℝ} (hb : 0 < b)
    (hbpi : b < Real.pi) (heta : 0 < eta) (hetasmall : eta ≤ Real.sin b/4) :
    ∃ outer0 : ℝ, 0 < outer0 ∧ ∀ outer : ℝ, ∀ ho : 0 < outer,
      outer ≤ outer0 → ∀ alpha : ℝ, 0 < alpha → alpha < Real.sin b/4 →
      ∀ N : ℕ, 0 < N → ∀ (r tau cut inner : ℝ) (hi : 0 < inner),
        0 < r → r < 1 → 0 ≤ tau → cut ∈ Icc (0:ℝ) 1 →
        ∀ (j : ℕ) (s : ℂ), s ∈ dampingDomain r →
        signedOriginalKSNorm σ N (constructedSelector b eta alpha) r tau j s cut ≤
          ‖iteratedDeriv j (signedOriginalSectorIntegral σ N (constructedSelector b eta alpha)
            r tau b outer inner ho hi none) s‖ +
          signedMixedLeftSectorNorm σ N (constructedSelector b eta alpha)
            r tau b outer inner ho hi j s cut +
          signedRightCompactSectorNorm σ N (constructedSelector b eta alpha)
            r tau b outer inner ho hi j s cut := by
  obtain ⟨outer0, ho0, hzero⟩ :=
    signed_constructed_current_all_branch_derivatives_zero σ hb hbpi heta hetasmall
  refine ⟨outer0, ho0, ?_⟩
  intro outer ho hout alpha halpha hasmall N hN r tau cut inner hi hr hr1 htau hcut j s hs
  have hf := constructedSelector_regular b eta alpha
    (Real.sin_pos_of_pos_of_lt_pi hb hbpi) heta hetasmall halpha
  apply signed_originalKSNorm_le_sectors σ hσ N hN (constructedSelector b eta alpha) hf hr hr1 htau hcut
    b outer inner ho hi j s hs
  intro q lam
  exact hzero outer ho hout alpha halpha hasmall N q r tau lam inner hi j s

end
end IsingBulk.HT.Tail
