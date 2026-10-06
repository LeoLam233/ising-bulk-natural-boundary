import IsingBulk.Tail.HighKSBound
import IsingBulk.Tail.WeightedCurrentInterval
import IsingBulk.Tail.SectorCurrentExclusion
import IsingBulk.Tail.MixedLeftAsymptotic
import IsingBulk.Tail.CompactRightClosure

/-! Finite absolute domination of the literal original and small-current
source by its all-branch, mixed/left, and compact-right sectors. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First MeasureTheory Set
open scoped BigOperators Topology Classical

/-- Every nested assignment belongs to one of the three estimated categories.
The sum retains the norm of each actual sector value. -/
theorem nested_sector_norm_le_categories {N : ℕ}
    (F : Fin N × (Fin N → Fin 3) → ℂ) :
    (∑ qa, ‖F qa‖) ≤
      (∑ qa, if ∃ j, qa.2 j=2 then ‖F qa‖ else 0) +
      (∑ qa, if leftCompactAssignment qa.2 then ‖F qa‖ else 0) +
      (∑ qa, if ∀ i, qa.2 i=1 then ‖F qa‖ else 0) := by
  classical
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro qa _
  have hM : 0 ≤ (if ∃ j, qa.2 j=2 then ‖F qa‖ else 0) := by
    split_ifs <;> positivity
  have hL : 0 ≤ (if leftCompactAssignment qa.2 then ‖F qa‖ else 0) := by
    split_ifs <;> positivity
  have hR : 0 ≤ (if ∀ i, qa.2 i=1 then ‖F qa‖ else 0) := by
    split_ifs <;> positivity
  rcases sector_assignment_mixed_left_right_cases qa.2 with hm | hl | hr
  · rw [ite_eq_left hm]
    linarith
  · rw [ite_eq_left hl]
    linarith
  · rw [ite_eq_left hr]
    linarith

/-- The existing exact source decompositions give the finite norm bound as
soon as the all-branch small-current term is known to vanish. -/
theorem originalKSNorm_le_sectors_of_current_none_zero (N : ℕ) (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r tau cut : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (htau : 0 ≤ tau) (hcut : cut ∈ Icc (0:ℝ) 1)
    (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner) (j : ℕ) (s : ℂ)
    (hs : s ∈ dampingDomain r)
    (hzero : ∀ q : Fin N,
      smallCurrentSectorIntegral N f r tau cut q b outer inner ho hi none j s = 0) :
    originalKSNorm N f r tau j s cut ≤
      ‖iteratedDeriv j (originalSectorIntegral N f r tau b outer inner ho hi none) s‖ +
      mixedLeftSectorNorm N f r tau b outer inner ho hi j s cut +
      rightCompactSectorNorm N f r tau b outer inner ho hi j s cut := by
  classical
  have hK : ‖iteratedDeriv j (originalLowerIntegral N f r tau) s‖ ≤
      ‖iteratedDeriv j (originalSectorIntegral N f r tau b outer inner ho hi none) s‖ +
      (originalMixedSectorNorm N f r tau b outer inner ho hi j s +
        originalLeftCompactSectorNorm N f r tau b outer inner ho hi j s +
        originalRightCompactSectorNorm N f r tau b outer inner ho hi j s) := by
    rw [originalLower_sector_derivative N hN f hf hr hr1 htau b outer inner ho hi s hs j]
    calc
      _ ≤ ∑ label, ‖iteratedDeriv j
          (originalSectorIntegral N f r tau b outer inner ho hi label) s‖ :=
        norm_sum_le _ _
      _ = ‖iteratedDeriv j (originalSectorIntegral N f r tau b outer inner ho hi none) s‖ +
          ∑ qa, ‖iteratedDeriv j
            (originalSectorIntegral N f r tau b outer inner ho hi (some qa)) s‖ := by
        rw [Fintype.sum_option]
      _ ≤ _ := by
        apply add_le_add le_rfl
        simpa only [originalMixedSectorNorm, originalLeftCompactSectorNorm,
          originalRightCompactSectorNorm] using
          nested_sector_norm_le_categories (fun qa => iteratedDeriv j
            (originalSectorIntegral N f r tau b outer inner ho hi (some qa)) s)
  have hS : ‖∫ lam in 0..cut, differentiatedCurrentSlice N f r tau lam j s‖ ≤
      integratedMixedSectorNorm N f r tau b outer inner ho hi j s cut +
        integratedLeftCompactSectorNorm N f r tau b outer inner ho hi j s cut +
        integratedRightCompactSectorNorm N f r tau b outer inner ho hi j s cut := by
    rw [small_current_sector_decomposition N hN f hf hr hr1 htau hcut
      b outer inner ho hi j hs]
    calc
      _ ≤ ∑ q : Fin N, ‖∑ label,
          smallCurrentSectorIntegral N f r tau cut q b outer inner ho hi label j s‖ :=
        norm_sum_le _ _
      _ ≤ ∑ q : Fin N, ∑ label,
          ‖smallCurrentSectorIntegral N f r tau cut q b outer inner ho hi label j s‖ := by
        apply Finset.sum_le_sum
        intro q _
        exact norm_sum_le _ _
      _ = ∑ q : Fin N, ∑ qa : Fin N × (Fin N → Fin 3),
          ‖smallCurrentSectorIntegral N f r tau cut q b outer inner ho hi (some qa) j s‖ := by
        apply Finset.sum_congr rfl
        intro q _
        rw [Fintype.sum_option, hzero q, norm_zero, zero_add]
      _ ≤ ∑ q : Fin N,
          ((∑ qa : Fin N × (Fin N → Fin 3), if ∃ i, qa.2 i=2 then
            ‖smallCurrentSectorIntegral N f r tau cut q b outer inner ho hi (some qa) j s‖ else 0) +
          (∑ qa : Fin N × (Fin N → Fin 3), if leftCompactAssignment qa.2 then
            ‖smallCurrentSectorIntegral N f r tau cut q b outer inner ho hi (some qa) j s‖ else 0) +
          (∑ qa : Fin N × (Fin N → Fin 3), if ∀ i, qa.2 i=1 then
            ‖smallCurrentSectorIntegral N f r tau cut q b outer inner ho hi (some qa) j s‖ else 0)) := by
        apply Finset.sum_le_sum
        intro q _
        exact nested_sector_norm_le_categories (fun qa =>
          smallCurrentSectorIntegral N f r tau cut q b outer inner ho hi (some qa) j s)
      _ = _ := by
        simp only [Finset.sum_add_distrib, smallCurrentSectorIntegral,
          integratedMixedSectorNorm, integratedLeftCompactSectorNorm,
          integratedRightCompactSectorNorm]
  calc
    originalKSNorm N f r tau j s cut =
        ‖iteratedDeriv j (originalLowerIntegral N f r tau) s‖ +
        ‖∫ lam in 0..cut, differentiatedCurrentSlice N f r tau lam j s‖ := rfl
    _ ≤ (‖iteratedDeriv j (originalSectorIntegral N f r tau b outer inner ho hi none) s‖ +
        (originalMixedSectorNorm N f r tau b outer inner ho hi j s +
          originalLeftCompactSectorNorm N f r tau b outer inner ho hi j s +
          originalRightCompactSectorNorm N f r tau b outer inner ho hi j s)) +
        (integratedMixedSectorNorm N f r tau b outer inner ho hi j s cut +
          integratedLeftCompactSectorNorm N f r tau b outer inner ho hi j s cut +
          integratedRightCompactSectorNorm N f r tau b outer inner ho hi j s cut) :=
      add_le_add hK hS
    _ = _ := by
      unfold mixedLeftSectorNorm rightCompactSectorNorm
      ring

/-- Derivative-level current exclusion is sufficient for the exact finite
source domination. It is supplied by the constructed selector below. -/
theorem originalKSNorm_le_sectors (N : ℕ) (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r tau cut : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (htau : 0 ≤ tau) (hcut : cut ∈ Icc (0:ℝ) 1)
    (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner) (j : ℕ) (s : ℂ)
    (hs : s ∈ dampingDomain r)
    (hzero : ∀ (q : Fin N) (lam : ℝ), iteratedDeriv j
      (currentSectorIntegral N f r tau lam q b outer inner ho hi none) s = 0) :
    originalKSNorm N f r tau j s cut ≤
      ‖iteratedDeriv j (originalSectorIntegral N f r tau b outer inner ho hi none) s‖ +
      mixedLeftSectorNorm N f r tau b outer inner ho hi j s cut +
      rightCompactSectorNorm N f r tau b outer inner ho hi j s cut := by
  apply originalKSNorm_le_sectors_of_current_none_zero N hN f hf hr hr1 htau hcut
    b outer inner ho hi j s hs
  intro q
  simp only [smallCurrentSectorIntegral, hzero q, intervalIntegral.integral_zero]

/-- The constructed source satisfies the domination without any additional
analytic or norm estimate premise. The outer cap is chosen before the source
radius, homotopy parameters, particle number, and derivative order. -/
theorem constructed_originalKSNorm_le_sectors {b eta : ℝ} (hb : 0 < b)
    (hbpi : b < Real.pi) (heta : 0 < eta) (hetasmall : eta ≤ Real.sin b/4) :
    ∃ outer0 : ℝ, 0 < outer0 ∧ ∀ outer : ℝ, ∀ ho : 0 < outer,
      outer ≤ outer0 → ∀ alpha : ℝ, 0 < alpha → alpha < Real.sin b/4 →
      ∀ N : ℕ, 0 < N → ∀ (r tau cut inner : ℝ) (hi : 0 < inner),
        0 < r → r < 1 → 0 ≤ tau → cut ∈ Icc (0:ℝ) 1 →
        ∀ (j : ℕ) (s : ℂ), s ∈ dampingDomain r →
        originalKSNorm N (constructedSelector b eta alpha) r tau j s cut ≤
          ‖iteratedDeriv j (originalSectorIntegral N (constructedSelector b eta alpha)
            r tau b outer inner ho hi none) s‖ +
          mixedLeftSectorNorm N (constructedSelector b eta alpha)
            r tau b outer inner ho hi j s cut +
          rightCompactSectorNorm N (constructedSelector b eta alpha)
            r tau b outer inner ho hi j s cut := by
  obtain ⟨outer0, ho0, hzero⟩ :=
    constructed_current_all_branch_derivatives_zero hb hbpi heta hetasmall
  refine ⟨outer0, ho0, ?_⟩
  intro outer ho hout alpha halpha hasmall N hN r tau cut inner hi hr hr1 htau hcut j s hs
  have hf := constructedSelector_regular b eta alpha
    (Real.sin_pos_of_pos_of_lt_pi hb hbpi) heta hetasmall halpha
  apply originalKSNorm_le_sectors N hN (constructedSelector b eta alpha) hf hr hr1 htau hcut
    b outer inner ho hi j s hs
  intro q lam
  exact hzero outer ho hout alpha halpha hasmall N q r tau lam inner hi j s

end
end IsingBulk.Tail
