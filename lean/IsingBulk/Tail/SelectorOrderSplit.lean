import IsingBulk.Tail.SelectorDerivativeDistribution
import IsingBulk.Tail.HighKSBound

/-! The real homotopy split is evaluated only after the full source
parameter derivative and interval integrability have been proved. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First MeasureTheory Set
open scoped BigOperators Topology

theorem selector_iteratedDeriv_split (N : ℕ) (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r tau cut : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (htau : 0 ≤ tau) (hcut : cut ∈ Icc (0:ℝ) 1)
    {s : ℂ} (hs : s ∈ dampingDomain r) (j : ℕ) :
    iteratedDeriv j (upperFormFactor N) s =
      iteratedDeriv j (selectedIntegral N f r tau) s +
      iteratedDeriv j (originalLowerIntegral N f r tau) s +
      (∫ lam : ℝ in 0..cut, differentiatedCurrentSlice N f r tau lam j s) +
      (∫ lam : ℝ in cut..1, differentiatedCurrentSlice N f r tau lam j s) := by
  have hj := (currentIntegral_iteratedDeriv_integrable N hN f hr hr1 htau
    hf.p_smooth hf.m_smooth hf.a_smooth hf.p_nonneg hf.m_nonneg hf.m_le_one
    hf.p_zero hf.m_zero j hs).1
  have hleft : IntervalIntegrable (fun lam => differentiatedCurrentSlice N f r tau lam j s) volume 0 cut := by
    apply hj.mono_set
    rw [uIcc_of_le hcut.1,uIcc_of_le (by norm_num : (0:ℝ)≤1)]
    exact Icc_subset_Icc le_rfl hcut.2
  have hright : IntervalIntegrable (fun lam => differentiatedCurrentSlice N f r tau lam j s) volume cut 1 := by
    apply hj.mono_set
    rw [uIcc_of_le hcut.2,uIcc_of_le (by norm_num : (0:ℝ)≤1)]
    exact Icc_subset_Icc hcut.1 le_rfl
  rw [selector_iteratedDeriv_full_current N hN f hf hr hr1 htau hs j,
    ← intervalIntegral.integral_add_adjacent_intervals hleft hright]
  ring

theorem selector_derivative_norm_split (N : ℕ) (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r tau cut : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (htau : 0 ≤ tau) (hcut : cut ∈ Icc (0:ℝ) 1)
    {s : ℂ} (hs : s ∈ dampingDomain r) (j : ℕ) :
    ‖iteratedDeriv j (upperFormFactor N) s‖ ≤
      ‖iteratedDeriv j (selectedIntegral N f r tau) s‖ + originalKSNorm N f r tau j s cut +
        ‖∫ lam : ℝ in cut..1, differentiatedCurrentSlice N f r tau lam j s‖ := by
  rw [selector_iteratedDeriv_split N hN f hf hr hr1 htau hcut hs j]
  unfold originalKSNorm
  calc
    _ ≤ ‖iteratedDeriv j (selectedIntegral N f r tau) s +
          iteratedDeriv j (originalLowerIntegral N f r tau) s +
          ∫ lam : ℝ in 0..cut, differentiatedCurrentSlice N f r tau lam j s‖ +
          ‖∫ lam : ℝ in cut..1, differentiatedCurrentSlice N f r tau lam j s‖ := norm_add_le _ _
    _ ≤ _ := by grw [norm_add_le,norm_add_le]; ring_nf; exact le_rfl

end
end IsingBulk.Tail
