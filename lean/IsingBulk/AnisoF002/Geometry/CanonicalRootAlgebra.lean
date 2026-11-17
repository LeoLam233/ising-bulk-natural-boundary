import IsingBulk.AnisoF002.Geometry.EndpointBridge
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# The actual interior spectral root: algebra and simplicity

Frozen and published F002, Lemma `lem:canonicalroot`.  The reciprocal
quadratic has exactly one root in the open unit disk off the real segment.
The final statements attach this argument to the literal physical spectral
polynomial, including `spectralS z = 0`.  No historical root theorem is used.
Analytic gluing, compact gaps, and positive-real physical identification are
separate obligations and are not asserted by the algebraic result.
-/

namespace IsingBulk.AnisoF002.Geometry
noncomputable section
open IsingBulk.Anisotropic

theorem unit_reciprocal_root_forces_real_segment {W r : ℂ}
    (hp : r ^ 2 - 2 * W * r + 1 = 0) (hn : ‖r‖ = 1) :
    ∃ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 ∧ W = (u : ℂ) := by
  have hr : r ≠ 0 := by intro h; simp [h] at hn
  have hsq : Complex.normSq r = 1 := by rw [Complex.normSq_eq_norm_sq, hn]; norm_num
  have hi : r⁻¹ = star r := by rw [Complex.inv_def, hsq]; simp
  have hsum : 2 * W = r + r⁻¹ := by
    apply (mul_right_cancel₀ hr)
    field_simp
    linear_combination -hp
  have hreal : W = (r.re : ℂ) := by
    apply (mul_left_cancel₀ (show (2 : ℂ) ≠ 0 by norm_num))
    rw [hsum, hi]
    apply Complex.ext <;> simp [two_mul]
  refine ⟨r.re, ?_, hreal⟩
  have h := Complex.abs_re_le_norm r
  rw [hn] at h
  exact abs_le.mp h

theorem reciprocal_small_root_unique {W r s : ℂ}
    (hr : r ^ 2 - 2 * W * r + 1 = 0) (hs : s ^ 2 - 2 * W * s + 1 = 0)
    (hnr : ‖r‖ < 1) (hns : ‖s‖ < 1) : r = s := by
  have hf : (r - s) * (r * s - 1) = 0 := by linear_combination s * hr - r * hs
  rcases mul_eq_zero.mp hf with h | h
  · exact sub_eq_zero.mp h
  · have hp := congrArg norm (sub_eq_zero.mp h)
    simp only [norm_mul, norm_one] at hp
    have hlt : ‖r‖ * ‖s‖ < 1 :=
      (mul_le_mul_of_nonneg_left hns.le (norm_nonneg r)).trans_lt (by simpa using hnr)
    linarith

theorem exists_unique_reciprocal_small_root {W : ℂ}
    (hW : ¬ ∃ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 ∧ W = (u : ℂ)) :
    ∃! r : ℂ, r ^ 2 - 2 * W * r + 1 = 0 ∧ ‖r‖ < 1 := by
  let d : ℂ := (W ^ 2 - 1) ^ ((2 : ℂ)⁻¹)
  have hd : d ^ 2 = W ^ 2 - 1 := by
    exact Complex.cpow_nat_inv_pow (W ^ 2 - 1) (show (2 : ℕ) ≠ 0 by decide)
  have hp : (W + d) ^ 2 - 2 * W * (W + d) + 1 = 0 := by linear_combination hd
  have hm : (W - d) ^ 2 - 2 * W * (W - d) + 1 = 0 := by linear_combination hd
  have hprod : (W + d) * (W - d) = 1 := by linear_combination -hd
  have hnorm := congrArg norm hprod
  simp only [norm_mul, norm_one] at hnorm
  have hne : ‖W + d‖ ≠ 1 := fun h => hW (unit_reciprocal_root_forces_real_segment hp h)
  have hex : ∃ r : ℂ, r ^ 2 - 2 * W * r + 1 = 0 ∧ ‖r‖ < 1 := by
    by_cases hlt : ‖W + d‖ < 1
    · exact ⟨W + d, hp, hlt⟩
    · have hgt : 1 < ‖W + d‖ := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hne)
      refine ⟨W - d, hm, ?_⟩
      by_contra h
      have hg := mul_le_mul_of_nonneg_left (le_of_not_gt h) (norm_nonneg (W + d))
      nlinarith
  obtain ⟨r, hr, hn⟩ := hex
  exact ⟨r, ⟨hr, hn⟩, fun s hs => reciprocal_small_root_unique hs.1 hr hs.2 hn⟩

theorem reciprocal_small_root_simple {W r : ℂ}
    (hp : r ^ 2 - 2 * W * r + 1 = 0) (hn : ‖r‖ < 1) :
    2 * r - 2 * W ≠ 0 := by
  intro h
  have hs : r ^ 2 = 1 := by linear_combination -hp + r * h
  have hns := congrArg norm hs
  simp only [norm_pow, norm_one] at hns
  nlinarith [norm_nonneg r]

/-- The exact polynomial in F002 Lemma 2.5, without division by `S`. -/
def spectralRootPolynomialF002 (lam : ℝ) (z : ℂ) (q : ℝ) (r : ℂ) : ℂ :=
  spectralS z * r ^ 2 -
    2 * (spectralA lam z - spectralT lam z * (Real.cos q : ℂ)) * r + spectralS z

theorem exists_unique_spectral_small_root {lam : ℝ} {z : ℂ} (q : ℝ)
    (hz : ¬ ∃ u ∈ Set.Icc (-1 : ℝ) 1, ∃ v ∈ Set.Icc (-1 : ℝ) 1,
      spectralA lam z = spectralS z * (u : ℂ) + spectralT lam z * (v : ℂ)) :
    ∃! r : ℂ, spectralRootPolynomialF002 lam z q r = 0 ∧ ‖r‖ < 1 := by
  let S := spectralS z
  let C := spectralA lam z - spectralT lam z * (Real.cos q : ℂ)
  have hq : Real.cos q ∈ Set.Icc (-1 : ℝ) 1 := ⟨Real.neg_one_le_cos q, Real.cos_le_one q⟩
  by_cases hS : S = 0
  · have hC : C ≠ 0 := by
      intro hc
      apply hz
      refine ⟨0, by norm_num, Real.cos q, hq, ?_⟩
      change spectralA lam z = S * 0 + spectralT lam z * (Real.cos q : ℂ)
      change spectralA lam z - spectralT lam z * (Real.cos q : ℂ) = 0 at hc
      simp only [mul_zero, zero_add]
      exact sub_eq_zero.mp hc
    refine ⟨0, ⟨?_, by norm_num⟩, ?_⟩
    · change S * 0 ^ 2 - 2 * C * 0 + S = 0
      simp [hS]
    · intro r hr
      have he : -(2 * C * r) = 0 := by
        have hpoly : S * r ^ 2 - 2 * C * r + S = 0 := hr.1
        simpa only [hS, zero_mul, zero_sub, add_zero] using hpoly
      exact (mul_eq_zero.mp (neg_eq_zero.mp he)).resolve_left (mul_ne_zero (by norm_num) hC)
  · have hW : ¬ ∃ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 ∧ C / S = (u : ℂ) := by
      rintro ⟨u, hu, he⟩
      apply hz
      refine ⟨u, hu, Real.cos q, hq, ?_⟩
      have hc : C = (u : ℂ) * S := (div_eq_iff hS).mp he
      change spectralA lam z - spectralT lam z * (Real.cos q : ℂ) = (u : ℂ) * S at hc
      change spectralA lam z = S * (u : ℂ) + spectralT lam z * (Real.cos q : ℂ)
      linear_combination hc
    have heq (r : ℂ) : spectralRootPolynomialF002 lam z q r = 0 ↔
        r ^ 2 - 2 * (C / S) * r + 1 = 0 := by
      have hid : spectralRootPolynomialF002 lam z q r =
          S * (r ^ 2 - 2 * (C / S) * r + 1) := by
        change S * r ^ 2 - 2 * C * r + S = _
        field_simp
      rw [hid]
      exact mul_eq_zero.trans (or_iff_right hS)
    obtain ⟨r, hr, hu⟩ := exists_unique_reciprocal_small_root hW
    refine ⟨r, ⟨(heq r).mpr hr.1, hr.2⟩, ?_⟩
    intro s hs
    exact hu s ⟨(heq s).mp hs.1, hs.2⟩

theorem quadratic_small_root_simple {S C r : ℂ}
    (hSC : S ≠ 0 ∨ C ≠ 0)
    (hp : S * r ^ 2 - 2 * C * r + S = 0) (hn : ‖r‖ < 1) :
    2 * S * r - 2 * C ≠ 0 := by
  intro hd
  by_cases hS : S = 0
  · have hC := hSC.resolve_left (not_not.mpr hS)
    have hc : C = 0 := by simpa [hS] using hd
    exact hC hc
  · have hf : S * (r ^ 2 - 1) = 0 := by linear_combination -hp + r * hd
    have hr : r ^ 2 = 1 := sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_left hS)
    have hnorm := congrArg norm hr
    simp only [norm_pow, norm_one] at hnorm
    nlinarith [norm_nonneg r]

theorem spectral_coefficients_nondegenerate {lam : ℝ} {z : ℂ} (q : ℝ)
    (hz : ¬ ∃ u ∈ Set.Icc (-1 : ℝ) 1, ∃ v ∈ Set.Icc (-1 : ℝ) 1,
      spectralA lam z = spectralS z * (u : ℂ) + spectralT lam z * (v : ℂ)) :
    spectralS z ≠ 0 ∨ spectralA lam z - spectralT lam z * (Real.cos q : ℂ) ≠ 0 := by
  by_contra hn
  push Not at hn
  apply hz
  refine ⟨0, by norm_num, Real.cos q, ⟨Real.neg_one_le_cos q, Real.cos_le_one q⟩, ?_⟩
  simp only [Complex.ofReal_zero, mul_zero, zero_add]
  exact sub_eq_zero.mp hn.2

/-- A total choice of the genuine small root; the fallback outside its
existence set has no mathematical use in the analytic/spectral theorems. -/
def spectralSmallRootF002 (lam : ℝ) (z : ℂ) (q : ℝ) : ℂ := by
  classical
  exact if h : ∃ r : ℂ, spectralRootPolynomialF002 lam z q r = 0 ∧ ‖r‖ < 1
    then h.choose else 0

theorem spectralSmallRootF002_spec {lam : ℝ} {z : ℂ} (q : ℝ)
    (hz : ¬ ∃ u ∈ Set.Icc (-1 : ℝ) 1, ∃ v ∈ Set.Icc (-1 : ℝ) 1,
      spectralA lam z = spectralS z * (u : ℂ) + spectralT lam z * (v : ℂ)) :
    spectralRootPolynomialF002 lam z q (spectralSmallRootF002 lam z q) = 0 ∧
      ‖spectralSmallRootF002 lam z q‖ < 1 := by
  have he := (exists_unique_spectral_small_root q hz).exists
  simp only [spectralSmallRootF002, dite_eq_left he]
  exact he.choose_spec

theorem spectralSmallRootF002_unique {lam : ℝ} {z : ℂ} (q : ℝ)
    (hz : ¬ ∃ u ∈ Set.Icc (-1 : ℝ) 1, ∃ v ∈ Set.Icc (-1 : ℝ) 1,
      spectralA lam z = spectralS z * (u : ℂ) + spectralT lam z * (v : ℂ))
    {r : ℂ} (hp : spectralRootPolynomialF002 lam z q r = 0) (hn : ‖r‖ < 1) :
    r = spectralSmallRootF002 lam z q :=
  (exists_unique_spectral_small_root q hz).unique ⟨hp, hn⟩ (spectralSmallRootF002_spec q hz)

theorem spectralSmallRootF002_simple {lam : ℝ} {z : ℂ} (q : ℝ)
    (hz : ¬ ∃ u ∈ Set.Icc (-1 : ℝ) 1, ∃ v ∈ Set.Icc (-1 : ℝ) 1,
      spectralA lam z = spectralS z * (u : ℂ) + spectralT lam z * (v : ℂ)) :
    2 * spectralS z * spectralSmallRootF002 lam z q -
      2 * (spectralA lam z - spectralT lam z * (Real.cos q : ℂ)) ≠ 0 :=
  quadratic_small_root_simple (spectral_coefficients_nondegenerate q hz)
    (spectralSmallRootF002_spec q hz).1 (spectralSmallRootF002_spec q hz).2

end
end IsingBulk.AnisoF002.Geometry
