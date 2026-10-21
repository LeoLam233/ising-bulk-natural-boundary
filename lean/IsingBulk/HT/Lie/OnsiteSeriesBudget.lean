import IsingBulk.HT.Lie.OnsiteCurrentInterval
import IsingBulk.HT.Contour.OnsiteSectorPartition
import IsingBulk.HT.Contour.OnsiteSelectorDerivatives
import IsingBulk.HT.Contour.OnsiteOddSelectedSeries
import IsingBulk.Tail.GlobalAnalytic

/-! Exact full-interval onsite reconstruction and numerical all-particle
Gaussian summation. These lemmas are used below by actual geometry endpoints. -/
namespace IsingBulk.HT.Lie
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail IsingBulk.HT.Contour IsingBulk.HT.Final
  Set Filter MeasureTheory Asymptotics
open scoped Topology BigOperators ContDiff

theorem onsite_selector_iteratedDeriv_full_current (N : ℕ) (hN : 0<N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ : ℝ}
    (hr : 0<r) (hr1 : r<1) (hτ : 0≤τ) {s : ℂ} (hs : s∈dampingDomain r) (j : ℕ) :
    iteratedDeriv j (upperOnsiteFormFactor N) s=
      iteratedDeriv j (onsiteSelectedIntegral N f r τ) s+
      iteratedDeriv j (onsiteOriginalLowerIntegral N f r τ) s+
      ∫ lam in (0:ℝ)..1,onsiteDifferentiatedCurrentSlice N f r τ lam j s := by
  rw [upperOnsiteFormFactor_selector_iteratedDeriv N hN f hf hr hr1 hτ hs j,
    onsite_currentIntegral_iteratedDeriv N hN f hr hr1 hτ hf.p_smooth hf.m_smooth hf.a_smooth
      hf.p_nonneg hf.m_nonneg hf.m_le_one hf.p_zero hf.m_zero j hs]

theorem onsite_original_derivative_sector_bound (N : ℕ) (hN : 0<N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ : ℝ}
    (hr : 0<r) (hr1 : r<1) (hτ : 0≤τ) (b inner : ℝ) (hi : 0< inner)
    {s : ℂ} (hs : s∈dampingDomain r) (j : ℕ) {Q : ℝ}
    (hbound : ∀ sigma,‖iteratedDeriv j (onsiteOriginalSectorIntegral N f r τ b inner hi sigma) s‖≤Q) :
    ‖iteratedDeriv j (onsiteOriginalLowerIntegral N f r τ) s‖≤3^N*Q := by
  classical
  rw [onsite_originalLower_sector_derivative N hN f hf hr hr1 hτ b inner hi hs j]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _sigma : Fin N → Fin 3,Q := Finset.sum_le_sum (fun sigma _ => hbound sigma)
    _ = _ := by simp

theorem onsite_current_derivative_sector_bound (N : ℕ) (hN : 0<N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ : ℝ}
    (hr : 0<r) (hr1 : r<1) (hτ : 0≤τ) (b inner : ℝ) (hi : 0< inner)
    {s : ℂ} (hs : s∈dampingDomain r) (j : ℕ) {Q : ℝ}
    (hbound : ∀ lam∈Icc (0:ℝ) 1,∀ q sigma,
      ‖iteratedDeriv j (onsiteNamedSectorIntegral N f r τ lam b inner hi q sigma) s‖≤Q) :
    ‖iteratedDeriv j (onsiteCurrentIntegral N f r τ) s‖≤(N:ℝ)*3^N*Q := by
  rw [onsite_currentIntegral_iteratedDeriv N hN f hr hr1 hτ hf.p_smooth hf.m_smooth hf.a_smooth
    hf.p_nonneg hf.m_nonneg hf.m_le_one hf.p_zero hf.m_zero j hs]
  have hslice (lam : ℝ) (hlam : lam∈Icc (0:ℝ) 1) :
      ‖onsiteDifferentiatedCurrentSlice N f r τ lam j s‖≤(N:ℝ)*3^N*Q := by
    classical
    rw [onsite_differentiatedCurrentSlice_sector_derivative N hN f hf hr hr1 hτ hlam.1 b inner hi hs j]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _q : Fin N,∑ _sigma : Fin N → Fin 3,Q := by
        apply Finset.sum_le_sum
        intro q _
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun sigma _ => hbound lam hlam q sigma))
      _ = _ := by simp [mul_assoc]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (C := (N:ℝ)*3^N*Q) (a := (0:ℝ)) (b := 1)
    (f := fun lam => onsiteDifferentiatedCurrentSlice N f r τ lam j s) (by
      intro lam hlam
      rw [uIoc_of_le (by norm_num : (0:ℝ)≤1)] at hlam
      exact hslice lam ⟨hlam.1.le,hlam.2⟩)
  simpa using hh

/-- Every infinite odd particle sum under one Gaussian envelope is bounded
uniformly in the radial parameter, hence smaller than every inverse power. -/
theorem onsite_odd_gaussian_series_subpower (E : ℝ → ℕ → ℝ)
    {C κ : ℝ} (m : ℕ) (hC : 0≤C) (hκ : 0<κ)
    (hE : ∀ eps n,0≤E eps n)
    (hmajor : ∀ᶠ eps : ℝ in 𝓝[>] 0,∀ n,E eps n≤
      C^(2*n+1)*((2*n+1:ℕ):ℝ)^m*Real.exp (-κ*((2*n+1:ℕ):ℝ)^2)) :
    (∀ᶠ eps : ℝ in 𝓝[>] 0,Summable (E eps)) ∧
      ∀ δ : ℝ,0<δ → (fun eps : ℝ => ∑' n,E eps n) =o[𝓝[>] 0] (fun eps : ℝ => eps^(-δ)) := by
  let S := fun n : ℕ => C^(2*n+1)*((2*n+1:ℕ):ℝ)^m*Real.exp (-κ*((2*n+1:ℕ):ℝ)^2)
  have hS : Summable S := (summable_source_gaussian hC hκ m).comp_injective
    (show Function.Injective (fun n : ℕ => 2*n+1) by intro a b h; dsimp only at h; omega)
  have hsum : ∀ᶠ eps : ℝ in 𝓝[>] 0,Summable (E eps) := by
    filter_upwards [hmajor] with eps heps
    exact Summable.of_nonneg_of_le (hE eps) heps hS
  refine ⟨hsum,?_⟩
  intro δ hδ
  have hb : (fun eps : ℝ => ∑' n,E eps n) =O[𝓝[>] 0] (fun _ : ℝ => (1:ℝ)) := by
    apply IsBigO.of_bound (∑' n,S n)
    filter_upwards [hmajor,hsum] with eps heps hs
    have hh := Summable.tsum_le_tsum heps hs hS
    simpa only [Real.norm_eq_abs,abs_of_nonneg (tsum_nonneg (hE eps)),norm_one,mul_one] using hh
  have hOne : (fun _ : ℝ => (1:ℝ)) =o[𝓝[>] 0] (fun eps : ℝ => eps^(-δ)) := by
    simpa only [zero_mul,Real.exp_zero] using radial_log_square_growth_littleO_rpow 0 hδ
  exact hb.trans_isLittleO hOne

end
end IsingBulk.HT.Lie
