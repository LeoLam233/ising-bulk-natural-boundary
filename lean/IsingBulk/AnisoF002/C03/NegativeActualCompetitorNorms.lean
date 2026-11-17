import IsingBulk.AnisoF002.C03.NegativeActualCompetitors

/-!
# Absolute sums of every actual complex-model competitor

This converts the full two-sided logarithmic estimate into the actual
sum of complex moduli.  Nonvanishing of the central physical-model
factors is supplied internally; no common phase is imposed.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Filter
open scoped BigOperators

theorem norm_le_norm_mul_exp_log_ratio (z w : ℂ) (hw : w ≠ 0) :
    ‖z‖ ≤ ‖w‖ * Real.exp (Real.log ‖z‖ - Real.log ‖w‖) := by
  calc
    _ ≤ Real.exp (Real.log ‖z‖) := Real.le_exp_log _
    _ = _ := by
      rw [Real.exp_sub, Real.exp_log (norm_pos_iff.mpr hw)]
      field_simp

theorem exists_actual_model_competitor_norm_sum {B : ℂ → ℂ}
    (hB : AnalyticAt ℂ B 0) (hslit : B 0 ∈ Complex.slitPlane)
    (c : ℝ) {s : ℝ} (hs : 0 < s) (d : ℕ) (hd : Even d) (hdpos : 0 < d) :
    ∃ T : ℝ, 0 < T ∧ ∀ N j K L : ℕ, Odd N → d ≤ N → d * L ≤ N →
      T ≤ Real.log j → Real.log j ≤ ((N - d * L : ℕ) : ℝ) →
      8 * (((N + d * K : ℕ) : ℝ)) ^ 2 ≤ (j : ℝ) →
      |actualModelLog B c s (N + d) j - actualModelLog B c s (N - d) j| ≤
        (d : ℝ) ^ 2 / 4 * Real.log j →
      let M : ℕ → ℂ := fun n => modelCoefficient n j (B (windingTau n : ℂ))
        (firstWindingCurvature n (B (windingTau n : ℂ)) c s) s (windingTau n)
      (∑ k ∈ Finset.range K, ‖M (N + d * (k + 1))‖) +
      (∑ k ∈ Finset.range L, ‖M (N - d * (k + 1))‖) ≤
      ‖M N‖ * (2 * (Real.exp (-((d : ℝ) ^ 2 * Real.log j) / 8) /
        (1 - Real.exp (-((d : ℝ) ^ 2 * Real.log j) / 8)))) := by
  obtain ⟨T₀, hT₀, hsum⟩ := exists_actual_model_competitor_log_sum hB hslit c hs d hd hdpos
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    (eventually_actual_model_factors_ne_zero hB.continuousAt (Complex.slitPlane_ne_zero hslit) c s)
  let T : ℝ := max T₀ ((N₀ : ℝ) + 1)
  refine ⟨T, hT₀.trans_le (le_max_left _ _), ?_⟩
  intro N j K L hN hdN hdL hjT hlow hhigh hcross
  let M : ℕ → ℂ := fun n => modelCoefficient n j (B (windingTau n : ℂ))
    (firstWindingCurvature n (B (windingTau n : ℂ)) c s) s (windingTau n)
  change (∑ k ∈ Finset.range K, ‖M (N + d * (k + 1))‖) +
    (∑ k ∈ Finset.range L, ‖M (N - d * (k + 1))‖) ≤ _
  have hlN : Real.log j ≤ (N : ℝ) :=
    hlow.trans (by exact_mod_cast Nat.sub_le N (d * L))
  have hN₀N : N₀ ≤ N := by
    have hh : (N₀ : ℝ) + 1 ≤ (N : ℝ) := (le_max_right _ _).trans (hjT.trans hlN)
    exact_mod_cast (show (N₀ : ℝ) ≤ N by linarith)
  have hf := hN₀ N hN₀N
  have hMN : M N ≠ 0 := modelCoefficient_ne_zero N j (B (windingTau N : ℂ))
    (firstWindingCurvature N (B (windingTau N : ℂ)) c s) s (windingTau N)
    hN.pos hf.2.1 hf.2.2 hs (windingTau_pos N hN.pos)
  have hpoint (a : ℕ) : ‖M a‖ ≤ ‖M N‖ *
      Real.exp (actualModelLog B c s a j - actualModelLog B c s N j) :=
    norm_le_norm_mul_exp_log_ratio (M a) (M N) hMN
  have hright : (∑ k ∈ Finset.range K, ‖M (N + d * (k + 1))‖) ≤
      ‖M N‖ * (∑ k ∈ Finset.range K, Real.exp
        (actualModelLog B c s (N + d * (k + 1)) j - actualModelLog B c s N j)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun k _ => hpoint (N + d * (k + 1)))
  have hleft : (∑ k ∈ Finset.range L, ‖M (N - d * (k + 1))‖) ≤
      ‖M N‖ * (∑ k ∈ Finset.range L, Real.exp
        (actualModelLog B c s (N - d * (k + 1)) j - actualModelLog B c s N j)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun k _ => hpoint (N - d * (k + 1)))
  have hb := hsum N j K L hN hdN hdL ((le_max_left _ _).trans hjT) hlow hhigh hcross
  have hm := mul_le_mul_of_nonneg_left hb (norm_nonneg (M N))
  change _ ≤ ‖M N‖ * _
  nlinarith only [hright, hleft, hm]

end
end IsingBulk.AnisoF002.NegativeHT
