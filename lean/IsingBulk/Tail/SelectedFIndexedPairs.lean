import IsingBulk.Tail.SelectedFPairMotion

/-! Collision-safe indexed pair estimates from compact-root motion.
No finite-order truncation and no division by a possibly zero pair product. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First

theorem compact_perturbed_pair_bounds {N : ℕ} (hN : 1 ≤ N)
    (J : Finset (Fin N)) (color : Fin N → Bool) (z₀ z : Fin N → ℂ)
    {g q D : ℝ} (hg : 0 < g) (_hq : q < 1) (hD : 0 ≤ D)
    (hD1 : D ≤ 1) (hDg : D ≤ g/6)
    (hDq : (4/g+12/g^2)*D ≤ (1-q)/2)
    (hn : ∀ i, ‖z₀ i‖ ≤ 1) (hi : ∀ i, (z₀ i).im ≤ 0)
    (hcover : ∀ i ∈ J, ‖z₀ i‖ ≤ 1-g ∨ (z₀ i).im ≤ -g)
    (hsame : ∀ i ∈ J, ∀ j ∈ J, color i=color j → ‖pairKernel (z₀ i) (z₀ j)‖ ≤ q)
    (hmove : ∀ i, ‖z i-z₀ i‖ ≤ D/(N:ℝ))
    (hfixed : ∀ i ∉ J, z i=z₀ i) :
    (∀ i ∈ J, ∀ j ∈ J, color i=color j → ‖pairKernel (z i) (z j)‖ ≤ (1+q)/2) ∧
    (∀ i j, i ∈ J ∨ j ∈ J → ‖pairKernel (z i) (z j)‖ ≤ 1+((4/g+12/g^2)*D)/(N:ℝ)) ∧
    (∀ i ∉ J, ∀ j ∉ J, ‖pairKernel (z i) (z j)‖ ≤ 1) := by
  have hn1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0:ℝ) < N := by linarith
  have hδ : 0 ≤ D/(N:ℝ) := div_nonneg hD hn0.le
  have hδD : D/(N:ℝ) ≤ D := div_le_self hD hn1
  have hbase (i j : Fin N) : ‖pairKernel (z₀ i) (z₀ j)‖ ≤ 1 :=
    schur_norm_le (hn i) (hn j) (mul_nonneg_of_nonpos_of_nonpos (hi i) (hi j))
  have hgap (i j : Fin N) (hij : i ∈ J ∨ j ∈ J) : g ≤ ‖1-z₀ i*z₀ j‖ := by
    rcases hij with h | h
    · rcases hcover i h with h | h
      · exact compact_norm_denominator_gap h (hn j)
      · exact compact_imaginary_denominator_gap hg.le (hn i) h (hi j)
    · have hh : g ≤ ‖1-z₀ j*z₀ i‖ := by
        rcases hcover j h with h | h
        · exact compact_norm_denominator_gap h (hn i)
        · exact compact_imaginary_denominator_gap hg.le (hn j) h (hi i)
      simpa only [mul_comm] using hh
  have hdiff (i j : Fin N) (hij : i ∈ J ∨ j ∈ J) :
      ‖pairKernel (z i) (z j)-pairKernel (z₀ i) (z₀ j)‖ ≤ ((4/g+12/g^2)*D)/(N:ℝ) := by
    have hh := pairKernel_two_coordinate_motion hg hδ (hδD.trans hD1) (hδD.trans hDg)
      (hn i) (hn j) (hmove i) (hmove j) (hgap i j hij)
    convert hh using 1
    ring
  have hK : 0 ≤ 4/g+12/g^2 := by positivity
  constructor
  · intro i hiJ j hjJ hcol
    have hh := norm_sub_norm_le (pairKernel (z i) (z j)) (pairKernel (z₀ i) (z₀ j))
    have hdiff' := hdiff i j (Or.inl hiJ)
    have hb := hsame i hiJ j hjJ hcol
    have hsc : ((4/g+12/g^2)*D)/(N:ℝ) ≤ (1-q)/2 :=
      (div_le_self (mul_nonneg hK hD) hn1).trans hDq
    linarith
  constructor
  · intro i j hij
    have hh := norm_sub_norm_le (pairKernel (z i) (z j)) (pairKernel (z₀ i) (z₀ j))
    have hd := hdiff i j hij
    have hb := hbase i j
    linarith
  · intro i hiJ j hjJ
    rw [hfixed i hiJ,hfixed j hjJ]
    exact hbase i j

end
end IsingBulk.Tail
