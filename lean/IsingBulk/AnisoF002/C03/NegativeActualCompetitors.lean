import IsingBulk.AnisoF002.C03.NegativeActualMiddleCurvature
import IsingBulk.AnisoF002.C03.NegativeSelectedWindowGates
import IsingBulk.AnisoF002.NegativeHT.DiscreteConcavity

/-!
# Complete two-sided competitor sums for the actual first-winding model

The actual middle-window curvature is propagated across every particle
in both finite prefixes.  Their combined bound is independent of either
prefix length.  Only an adjacent discrepancy at the selected center is
used; phases of competing complex model coefficients are unrestricted.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open scoped BigOperators

theorem exists_actual_model_competitor_log_sum {B : ℂ → ℂ}
    (hB : AnalyticAt ℂ B 0) (hslit : B 0 ∈ Complex.slitPlane)
    (c : ℝ) {s : ℝ} (hs : 0 < s) (d : ℕ) (hd : Even d) (hdpos : 0 < d) :
    ∃ T : ℝ, 0 < T ∧ ∀ N j K L : ℕ, Odd N → d ≤ N → d * L ≤ N →
      T ≤ Real.log j → Real.log j ≤ ((N - d * L : ℕ) : ℝ) →
      8 * (((N + d * K : ℕ) : ℝ)) ^ 2 ≤ (j : ℝ) →
      |actualModelLog B c s (N + d) j - actualModelLog B c s (N - d) j| ≤
        (d : ℝ) ^ 2 / 4 * Real.log j →
      (∑ k ∈ Finset.range K, Real.exp
        (actualModelLog B c s (N + d * (k + 1)) j - actualModelLog B c s N j)) +
      (∑ k ∈ Finset.range L, Real.exp
        (actualModelLog B c s (N - d * (k + 1)) j - actualModelLog B c s N j)) ≤
      2 * (Real.exp (-((d : ℝ) ^ 2 * Real.log j) / 8) /
        (1 - Real.exp (-((d : ℝ) ^ 2 * Real.log j) / 8))) := by
  obtain ⟨T, hT, hactual⟩ := exists_actual_model_middle_curvature hB hslit c hs d hd hdpos
  refine ⟨T, hT, ?_⟩
  intro N j K L hN hdN hdL hjT hlow hhigh hcross
  let f : ℕ → ℝ := fun k => actualModelLog B c s (N + d * k) j
  let g : ℕ → ℝ := fun k => actualModelLog B c s (N - d * k) j
  let κ : ℝ := (d : ℝ) ^ 2 / 2 * Real.log j
  have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hjlog : 0 < Real.log j := hT.trans_le hjT
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hlN : Real.log j ≤ (N : ℝ) :=
    hlow.trans (by exact_mod_cast Nat.sub_le N (d * L))
  have hupper {a : ℕ} (ha : a ≤ N + d * K) : 8 * (a : ℝ) ^ 2 ≤ (j : ℝ) := by
    have har : (a : ℝ) ≤ ((N + d * K : ℕ) : ℝ) := by exact_mod_cast ha
    have hp := pow_le_pow_left₀ (Nat.cast_nonneg a) har 2
    nlinarith
  have hc : f 1 - 2 * f 0 + g 1 ≤ -κ := by
    have hbase : Odd (N - d) := Nat.Odd.sub_even hdN hN hd
    have hsum : N - d + d = N := Nat.sub_add_cancel hdN
    have hsum2 : N - d + 2 * d = N + d := by omega
    have hh := hactual (N - d) j hbase hjT
      (by simpa only [← Nat.cast_add, hsum] using hlN)
      (by simpa only [← Nat.cast_add, hsum] using hupper (a := N) (by omega))
    simpa only [f, g, Nat.mul_one, Nat.mul_zero, Nat.add_zero, hsum, hsum2, κ, neg_mul] using hh
  have hf : ∀ k, k + 2 ≤ K → f (k + 2) - 2 * f (k + 1) + f k ≤ -κ := by
    intro k hk
    have hbase : Odd (N + d * k) := hN.add_even (hd.mul_right k)
    have hid1 : N + d * k + d = N + d * (k + 1) := by ring
    have hid2 : N + d * k + 2 * d = N + d * (k + 2) := by ring
    have hindex : N + d * (k + 1) ≤ N + d * K :=
      Nat.add_le_add_left (Nat.mul_le_mul_left d (by omega)) N
    have hlow' : Real.log j ≤ ((N + d * (k + 1) : ℕ) : ℝ) :=
      hlN.trans (by exact_mod_cast Nat.le_add_right N (d * (k + 1)))
    have hh := hactual (N + d * k) j hbase hjT
      (by simpa only [← Nat.cast_add, hid1] using hlow')
      (by simpa only [← Nat.cast_add, hid1] using hupper hindex)
    simpa only [f, hid1, hid2, κ, neg_mul] using hh
  have hg : ∀ k, k + 2 ≤ L → g (k + 2) - 2 * g (k + 1) + g k ≤ -κ := by
    intro k hk
    have hd2 : d * (k + 2) ≤ N :=
      (Nat.mul_le_mul_left d hk).trans hdL
    have hd1 : d * (k + 1) ≤ d * L := Nat.mul_le_mul_left d (by omega)
    have hd0 : d * k ≤ N :=
      (Nat.mul_le_mul_left d (show k ≤ k + 2 by omega)).trans hd2
    have hbase : Odd (N - d * (k + 2)) :=
      Nat.Odd.sub_even hd2 hN (hd.mul_right (k + 2))
    have hid1 : N - d * (k + 2) + d = N - d * (k + 1) := by
      simp only [Nat.mul_add, Nat.mul_one] at *
      omega
    have hid2 : N - d * (k + 2) + 2 * d = N - d * k := by
      simp only [Nat.mul_add, Nat.mul_one] at *
      omega
    have hloIndex : N - d * L ≤ N - d * (k + 1) := by omega
    have hlow' : Real.log j ≤ ((N - d * (k + 1) : ℕ) : ℝ) :=
      hlow.trans (by exact_mod_cast hloIndex)
    have hindex : N - d * (k + 1) ≤ N + d * K := by omega
    have hh := hactual (N - d * (k + 2)) j hbase hjT
      (by simpa only [← Nat.cast_add, hid1] using hlow')
      (by simpa only [← Nat.cast_add, hid1] using hupper hindex)
    rw [hid1, hid2] at hh
    dsimp [g, κ]
    linarith only [hh]
  have hcenter : |f 1 - g 1| ≤ κ / 2 := by
    simpa only [f, g, Nat.mul_one,
      show (d : ℝ) ^ 2 / 4 * Real.log j = κ / 2 by dsimp [κ]; ring] using hcross
  have hbound := two_sided_competitor_bound f g κ (κ / 2) K L hκ le_rfl
    (by simp [f, g]) hcenter hc hf hg
  simpa only [f, g, Nat.mul_zero, Nat.add_zero,
    show -κ / 4 = -((d : ℝ) ^ 2 * Real.log j) / 8 by dsimp [κ]; ring] using hbound

end
end IsingBulk.AnisoF002.NegativeHT
