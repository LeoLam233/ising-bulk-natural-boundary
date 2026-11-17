import IsingBulk.AnisoF002.C03.IsotropicFirstArithmeticData
import IsingBulk.AnisoF002.C03.IsotropicFirstPeriodAmplitude

/-!
# The full first singular order, scale and nonzero physical amplitude

The two actual parity orders have respectively the s² and s scales.
At that very order every later same-parity particle satisfies the
retained-pair estimate used for the complete infinite remainder.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.RegularTail.C03

theorem IsotropicFirstArithmeticData.exists_actual_first_scaling
    {m K : ℕ} {α phase : ℝ} {σ : ℂ}
    (h : IsotropicFirstArithmeticData m K α phase σ) :
    ∃ j l : ℕ, 0 < l ∧
      2 * j + 2 = m + 2 * K + 2 * (m + 2 * K + 1).choose 2 + l ∧
      j + 1 ≤ (m + 2 * (K + 1) + 1).choose 2 ∧
      (2 : ℂ) * isotropicFirstChartAmplitude (m + 2 * K) α j ≠ 0 := by
  have hfirst := h.first_count_ge_seven
  rcases h.offset_physical with hm | hm
  · subst m
    have hn : Odd (0 + 2 * K + 1) := ⟨K, by omega⟩
    refine ⟨oddTopOrder (0 + 2 * K + 1), 2, by norm_num,
      odd_first_scaling_degree hn, ?_, ?_⟩
    · exact isotropic_odd_all_later_retained_pair_budget (n := 0 + 2 * K + 1)
        (by omega) le_rfl
    · exact mul_ne_zero (by norm_num)
        (isotropicFirstChartAmplitude_odd_ne_zero (by omega) hn h.angle_pos h.angle_lt_half)
  · subst m
    have hn : Even (1 + 2 * K + 1) := ⟨K + 1, by omega⟩
    refine ⟨evenTopOrder (1 + 2 * K + 1), 1, by norm_num,
      even_first_scaling_degree hn, ?_, ?_⟩
    · exact isotropic_even_all_later_retained_pair_budget (n := 1 + 2 * K + 1)
        (by omega) le_rfl
    · exact mul_ne_zero (by norm_num)
        (isotropicFirstChartAmplitude_even_ne_zero hn h.angle_pos h.angle_lt_half)

end
end IsingBulk.AnisoF002.Isotropic
