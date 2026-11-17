import IsingBulk.AnisoF002.NegativeHT.DiscreteConcavity
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Complete-series noncancellation from absolute competitor sums

These are conditional assembly theorems for the full series. They impose no
common-phase condition. Their summability and aggregate dominance hypotheses
must still be proved for the actual F002 physical jets, including every
particle range and every analytic/model-error contribution.
-/

namespace IsingBulk.AnisoF002.NegativeHT

open scoped BigOperators

/-- The sum of all competitors, including infinitely many terms, bounds the
error of the complete series from its chosen term. -/
theorem complete_series_error_bound {ι : Type*} [DecidableEq ι]
    (f : ι → ℂ) (k : ι) (hf : Summable fun i => ‖f i‖) :
    ‖(∑' i, f i)-f k‖ ≤ ∑' i, ‖if i=k then (0:ℂ) else f i‖ := by
  have hr : Summable fun i => ‖if i=k then (0:ℂ) else f i‖ := by
    apply Summable.of_nonneg_of_le (fun i => norm_nonneg _) _ hf
    intro i
    split_ifs <;> simp
  have hs : Summable f := hf.of_norm
  rw [hs.tsum_eq_add_tsum_ite k]
  simpa using norm_tsum_le_tsum_norm hr

/-- Reverse triangle inequality for the complete series and its full absolute
competitor sum. No comparison of individual phases is used. -/
theorem complete_series_lower_bound {ι : Type*} [DecidableEq ι]
    (f : ι → ℂ) (k : ι) (hf : Summable fun i => ‖f i‖) :
    ‖f k‖ - (∑' i, ‖if i=k then (0:ℂ) else f i‖) ≤ ‖∑' i, f i‖ := by
  have he := complete_series_error_bound f k hf
  have hr := norm_sub_norm_le (f k) (∑' i, f i)
  rw [norm_sub_rev] at hr
  linarith

/-- Strict aggregate dominance proves nonvanishing of the complete sum. -/
theorem complete_series_ne_zero {ι : Type*} [DecidableEq ι]
    (f : ι → ℂ) (k : ι) (hf : Summable fun i => ‖f i‖)
    (hdominance : (∑' i, ‖if i=k then (0:ℂ) else f i‖) < ‖f k‖) :
    (∑' i, f i) ≠ 0 := by
  apply norm_pos_iff.mp
  have h := complete_series_lower_bound f k hf
  linarith

/-- Quantitative relative lower bound, suitable for a derivative subsequence. -/
theorem complete_series_relative_lower_bound {ι : Type*} [DecidableEq ι]
    (f : ι → ℂ) (k : ι) (hf : Summable fun i => ‖f i‖) (ε : ℝ)
    (hdominance : (∑' i, ‖if i=k then (0:ℂ) else f i‖) ≤ ε*‖f k‖) :
    (1-ε)*‖f k‖ ≤ ‖∑' i, f i‖ := by
  have h := complete_series_lower_bound f k hf
  nlinarith

/-- The two complete finite middle-window sums have an aggregate norm bound
that is independent of either window length. -/
theorem middle_window_norm_bound (f g : ℕ → ℝ) (u v : ℕ → ℂ)
    (c η M : ℝ) (K L : ℕ)
    (hc : 0<c) (hη : η≤c/2) (hM : 0≤M) (hzero : g 0=f 0)
    (hcenter : |f 1-g 1|≤η) (hcentralCurv : f 1-2*f 0+g 1≤-c)
    (hf : ∀ k, k+2≤K → f (k+2)-2*f (k+1)+f k≤-c)
    (hg : ∀ k, k+2≤L → g (k+2)-2*g (k+1)+g k≤-c)
    (hu : ∀ k ∈ Finset.range K, ‖u (k+1)‖ ≤ M*Real.exp (f (k+1)-f 0))
    (hv : ∀ k ∈ Finset.range L, ‖v (k+1)‖ ≤ M*Real.exp (g (k+1)-f 0)) :
    ‖(∑ k ∈ Finset.range K, u (k+1)) + (∑ k ∈ Finset.range L, v (k+1))‖ ≤
      M * (2 * (Real.exp (-c/4)/(1-Real.exp (-c/4)))) := by
  have hL : ‖∑ k ∈ Finset.range K, u (k+1)‖ ≤
      M*(∑ k ∈ Finset.range K, Real.exp (f (k+1)-f 0)) := by
    calc
      _ ≤ ∑ k ∈ Finset.range K, ‖u (k+1)‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range K, M*Real.exp (f (k+1)-f 0) := Finset.sum_le_sum hu
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hR : ‖∑ k ∈ Finset.range L, v (k+1)‖ ≤
      M*(∑ k ∈ Finset.range L, Real.exp (g (k+1)-f 0)) := by
    calc
      _ ≤ ∑ k ∈ Finset.range L, ‖v (k+1)‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range L, M*Real.exp (g (k+1)-f 0) := Finset.sum_le_sum hv
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hb := two_sided_competitor_bound f g c η K L hc hη hzero hcenter hcentralCurv hf hg
  have hm := mul_le_mul_of_nonneg_left hb hM
  have ht := norm_add_le (∑ k ∈ Finset.range K, u (k+1))
    (∑ k ∈ Finset.range L, v (k+1))
  nlinarith

/-- A finite middle window and the entire summable remainder are combined
before asserting noncancellation. The latter may encode low/high particle
ranges, higher windings, and analytic and model errors. -/
theorem assembled_series_lower_bound {ι : Type*} (main middle : ℂ)
    (rest : ι → ℂ) (q δ : ℝ) (hr : Summable fun i => ‖rest i‖)
    (hm : ‖middle‖ ≤ q*‖main‖)
    (ht : (∑' i, ‖rest i‖) ≤ δ*‖main‖) :
    (1-q-δ)*‖main‖ ≤ ‖main+middle+(∑' i, rest i)‖ := by
  have hs := norm_tsum_le_tsum_norm hr
  have hn := norm_add_le middle (∑' i, rest i)
  have hrev := norm_sub_norm_le main (-(middle+(∑' i, rest i)))
  simp only [norm_neg, sub_neg_eq_add] at hrev
  rw [← add_assoc] at hrev
  nlinarith

/-- Whole-series noncancellation after the complete remainder has been bounded. -/
theorem assembled_series_ne_zero {ι : Type*} (main middle : ℂ)
    (rest : ι → ℂ) (q δ : ℝ) (hr : Summable fun i => ‖rest i‖)
    (hmain : main ≠ 0) (hm : ‖middle‖ ≤ q*‖main‖)
    (ht : (∑' i, ‖rest i‖) ≤ δ*‖main‖) (hsmall : q+δ<1) :
    main+middle+(∑' i, rest i) ≠ 0 := by
  have hp : 0<‖main‖ := norm_pos_iff.mpr hmain
  have h := assembled_series_lower_bound main middle rest q δ hr hm ht
  apply norm_pos_iff.mp
  have : 0<(1-q-δ)*‖main‖ := mul_pos (by linarith) hp
  linarith

end IsingBulk.AnisoF002.NegativeHT
