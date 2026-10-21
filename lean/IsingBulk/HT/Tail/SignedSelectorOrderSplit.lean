import IsingBulk.HT.Tail.SignedSelectorDerivativeDistribution
import IsingBulk.HT.Tail.SignedHighKSBound

/-! The real homotopy split is evaluated only after the full source
parameter derivative and interval integrability have been proved. -/
namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour MeasureTheory Set
open scoped BigOperators Topology

theorem signed_selector_iteratedDeriv_split (σ : ℂ) (hσ : ‖σ‖ = 1) (N : ℕ) (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r tau cut : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (htau : 0 ≤ tau) (hcut : cut ∈ Icc (0:ℝ) 1)
    {s : ℂ} (hs : s ∈ dampingDomain r) (j : ℕ) :
    iteratedDeriv j (signedSourceIntegral σ N r) s =
      iteratedDeriv j (signedSelectedIntegral σ N f r tau) s +
      iteratedDeriv j (signedOriginalLowerIntegral σ N f r tau) s +
      (∫ lam : ℝ in 0..cut, signedDifferentiatedCurrentSlice σ N f r tau lam j s) +
      (∫ lam : ℝ in cut..1, signedDifferentiatedCurrentSlice σ N f r tau lam j s) := by
  have hj := (signed_currentIntegral_iteratedDeriv_integrable σ hσ N hN f hr hr1 htau
    hf.p_smooth hf.m_smooth hf.a_smooth hf.p_nonneg hf.m_nonneg hf.m_le_one
    hf.p_zero hf.m_zero j hs).1
  have hleft : IntervalIntegrable (fun lam => signedDifferentiatedCurrentSlice σ N f r tau lam j s) volume 0 cut := by
    apply hj.mono_set
    rw [uIcc_of_le hcut.1,uIcc_of_le (by norm_num : (0:ℝ)≤1)]
    exact Icc_subset_Icc le_rfl hcut.2
  have hright : IntervalIntegrable (fun lam => signedDifferentiatedCurrentSlice σ N f r tau lam j s) volume cut 1 := by
    apply hj.mono_set
    rw [uIcc_of_le hcut.2,uIcc_of_le (by norm_num : (0:ℝ)≤1)]
    exact Icc_subset_Icc hcut.1 le_rfl
  rw [signed_selector_iteratedDeriv_full_current σ hσ N hN f hf hr hr1 htau hs j,
    ← intervalIntegral.integral_add_adjacent_intervals hleft hright]
  ring

theorem signed_selector_derivative_norm_split (σ : ℂ) (hσ : ‖σ‖ = 1) (N : ℕ) (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r tau cut : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (htau : 0 ≤ tau) (hcut : cut ∈ Icc (0:ℝ) 1)
    {s : ℂ} (hs : s ∈ dampingDomain r) (j : ℕ) :
    ‖iteratedDeriv j (signedSourceIntegral σ N r) s‖ ≤
      ‖iteratedDeriv j (signedSelectedIntegral σ N f r tau) s‖ + signedOriginalKSNorm σ N f r tau j s cut +
        ‖∫ lam : ℝ in cut..1, signedDifferentiatedCurrentSlice σ N f r tau lam j s‖ := by
  rw [signed_selector_iteratedDeriv_split σ hσ N hN f hf hr hr1 htau hcut hs j]
  unfold signedOriginalKSNorm
  calc
    _ ≤ ‖iteratedDeriv j (signedSelectedIntegral σ N f r tau) s +
          iteratedDeriv j (signedOriginalLowerIntegral σ N f r tau) s +
          ∫ lam : ℝ in 0..cut, signedDifferentiatedCurrentSlice σ N f r tau lam j s‖ +
          ‖∫ lam : ℝ in cut..1, signedDifferentiatedCurrentSlice σ N f r tau lam j s‖ := norm_add_le _ _
    _ ≤ _ := by grw [norm_add_le,norm_add_le]; ring_nf; exact le_rfl

end
end IsingBulk.HT.Tail
