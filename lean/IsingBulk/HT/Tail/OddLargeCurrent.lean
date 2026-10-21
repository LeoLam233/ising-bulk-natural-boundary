import IsingBulk.Tail.LargeCurrentAsymptotic

/-!
# The entire differentiated odd large-current series

The LT source theorem `large_current_per_order` is genuinely all-N.  Only
its former summation wrapper selected even dimensions.  Here the very same
proved bound is summed over every positive odd particle number.  No upper
particle cutoff, finite truncation, or tail estimate is assumed.

This is the unsigned/positive-kernel upper-trace sector.  Transfer to the
negative-sign kernel is a separate HT obligation.
-/

namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail Set MeasureTheory Filter Asymptotics
open scoped Topology

theorem large_current_positive_odd_series (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta / 2) :
    ∃ eta0 : ℝ, 0 < eta0 ∧ ∀ eta : ℝ, 0 < eta → eta < eta0 →
      ∃ alpha0 tau0 : ℝ, 0 < alpha0 ∧ 0 < tau0 ∧ ∀ alpha tau : ℝ,
        0 < alpha → alpha < alpha0 → 0 < tau → tau < tau0 →
        ∃ eps0 : ℝ, 0 < eps0 ∧ ∀ j : ℕ, ∃ C : ℝ, 0 < C ∧
          ∀ eps lamStar : ℝ, 0 < eps → eps < eps0 → 0 < lamStar → lamStar ≤ 1 →
            Summable (fun n : ℕ => ‖∫ lam in lamStar..1,
              differentiatedCurrentSlice (2 * n + 1) (constructedSelector d.thetaB eta alpha)
                (Real.exp (-d.c₀ * eps)) tau lam j (radialParameter d.theta eps)‖) ∧
            (∑' n : ℕ, ‖∫ lam in lamStar..1,
              differentiatedCurrentSlice (2 * n + 1) (constructedSelector d.thetaB eta alpha)
                (Real.exp (-d.c₀ * eps)) tau lam j (radialParameter d.theta eps)‖) ≤
                  C * (lamStar⁻¹) ^ (j + 1) := by
  obtain ⟨eta0, heta0, hsetup⟩ := large_current_per_order d hcsmall
  refine ⟨eta0, heta0, ?_⟩
  intro eta heta hetaLt
  obtain ⟨alpha0, tau0, halpha0, htau0, hnext⟩ := hsetup eta heta hetaLt
  refine ⟨alpha0, tau0, halpha0, htau0, ?_⟩
  intro alpha tau halpha halphaLt htau htauLt
  obtain ⟨c, e, K, D, kappa, hc, he, hK, hD, hkappa, hbound⟩ :=
    hnext alpha tau halpha halphaLt htau htauLt
  refine ⟨e, he, ?_⟩
  intro j
  let A := (j.factorial : ℝ) * K / c ^ j
  let g : ℕ → ℝ := fun n => D ^ (2 * n + 1) * ((2 * n + 1 : ℕ) : ℝ) ^ (2 * j) *
    Real.exp (-kappa * ((2 * n + 1 : ℕ) : ℝ) ^ 2)
  have hA : 0 < A := by dsimp [A]; positivity
  have hg0 : ∀ n, 0 ≤ g n := by intro n; dsimp [g]; positivity
  have hg : Summable g := (summable_source_gaussian hD.le hkappa (2 * j)).comp_injective
    (show Function.Injective (fun n : ℕ => 2 * n + 1) by
      intro a b hab; dsimp at hab; omega)
  let C := A * ((∑' n, g n) + 1)
  have hC : 0 < C := by
    dsimp [C]
    have hh : 0 ≤ ∑' n, g n := tsum_nonneg hg0
    positivity
  refine ⟨C, hC, ?_⟩
  intro eps lamStar heps hepsLt hls hls1
  let L := (lamStar⁻¹) ^ (j + 1)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hpoint (n : ℕ) :
      ‖∫ lam in lamStar..1,
        differentiatedCurrentSlice (2 * n + 1) (constructedSelector d.thetaB eta alpha)
          (Real.exp (-d.c₀ * eps)) tau lam j (radialParameter d.theta eps)‖ ≤
        (A * L) * g n := by
    have hh := (hbound (2 * n + 1) j eps lamStar (by omega)
      heps hepsLt hls hls1).2
    convert hh using 1
    dsimp [A, L, g]
    ring
  have hdom := hg.mul_left (A * L)
  have hsum := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpoint hdom
  refine ⟨hsum, ?_⟩
  have hh := Summable.tsum_le_tsum hpoint hsum hdom
  rw [tsum_mul_left] at hh
  apply hh.trans
  dsimp only [C, L]
  nlinarith [mul_nonneg hA.le hL]

/-- The full infinite odd large-current series is negligible at the
inverse-square-root radial scale.  All parameter choices precede `j`, the
cutoff exponent and the radial limit. -/
theorem large_current_positive_odd_littleo (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta / 2) :
    ∃ eta0 : ℝ, 0 < eta0 ∧ ∀ eta : ℝ, 0 < eta → eta < eta0 →
      ∃ alpha0 tau0 : ℝ, 0 < alpha0 ∧ 0 < tau0 ∧ ∀ alpha tau : ℝ,
        0 < alpha → alpha < alpha0 → 0 < tau → tau < tau0 →
        ∀ (j : ℕ) (beta : ℝ), 0 < beta → beta * ((j : ℝ) + 1) < 1 / 2 →
          IsLittleO (𝓝[>] (0 : ℝ))
            (fun eps : ℝ => ∑' n : ℕ, ‖∫ lam in (eps ^ beta)..1,
              differentiatedCurrentSlice (2 * n + 1) (constructedSelector d.thetaB eta alpha)
                (Real.exp (-d.c₀ * eps)) tau lam j (radialParameter d.theta eps)‖)
            (fun eps : ℝ => (Real.sqrt eps)⁻¹) := by
  obtain ⟨eta0, heta0, hsetup⟩ := large_current_positive_odd_series d hcsmall
  refine ⟨eta0, heta0, ?_⟩
  intro eta heta hetaLt
  obtain ⟨alpha0, tau0, halpha0, htau0, hnext⟩ := hsetup eta heta hetaLt
  refine ⟨alpha0, tau0, halpha0, htau0, ?_⟩
  intro alpha tau halpha halphaLt htau htauLt j beta hbeta hexp
  obtain ⟨e, he, hseries⟩ := hnext alpha tau halpha halphaLt htau htauLt
  obtain ⟨C, hC, hbound⟩ := hseries j
  apply IsBigO.trans_isLittleO (g := fun eps : ℝ => ((eps ^ beta)⁻¹) ^ (j + 1))
    ?_ (cutoff_power_littleo_sqrt hexp)
  apply isBigO_iff.mpr
  refine ⟨C, ?_⟩
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds he),
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
    with eps heps hepse heps1
  have hl : 0 < eps ^ beta := Real.rpow_pos_of_pos heps _
  have hl1 : eps ^ beta ≤ 1 := Real.rpow_le_one heps.le heps1.le hbeta.le
  have hh := (hbound eps (eps ^ beta) heps hepse hl hl1).2
  have hnon : 0 ≤ ∑' n : ℕ, ‖∫ lam in (eps ^ beta)..1,
      differentiatedCurrentSlice (2 * n + 1) (constructedSelector d.thetaB eta alpha)
        (Real.exp (-d.c₀ * eps)) tau lam j (radialParameter d.theta eps)‖ :=
    tsum_nonneg (fun _ => norm_nonneg _)
  simpa only [Real.norm_eq_abs, abs_of_nonneg hnon,
    abs_of_nonneg (by positivity : 0 ≤ ((eps ^ beta)⁻¹) ^ (j + 1))] using hh

end
end IsingBulk.HT.Tail
