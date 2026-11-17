import IsingBulk.AnisoF002.C03.IsotropicFirstCompactDirections

/-!
# Lower bound for the original physical first denominator

The exact radial denominator is bounded below by epsilon plus the full
constrained quadratic radius. The compact-direction proof uses the original
canonical roots and retains every possible ratio of the two scales.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology BigOperators

theorem isotropic_first_normalized_direction {N : ℕ} {e : ℝ} (he : 0 < e)
    (u : Fin N → ℝ) :
    (e / (e + ∑ i, u i ^ 2), fun i => u i / Real.sqrt (e + ∑ k, u k ^ 2)) ∈
      isotropicFirstDirections N := by
  let Q := ∑ i, u i ^ 2
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hE : 0 < e + Q := add_pos_of_pos_of_nonneg he hQ
  have hs : 0 < Real.sqrt (e + Q) := Real.sqrt_pos.2 hE
  have hs2 : (Real.sqrt (e + Q)) ^ 2 = e + Q := Real.sq_sqrt hE.le
  have hsum : ∑ i, (u i / Real.sqrt (e + Q)) ^ 2 = Q / (e + Q) := by
    simp only [div_pow, hs2, ← Finset.sum_div, Q]
  refine ⟨⟨⟨div_nonneg he.le hE.le, (div_le_one hE).2 (le_add_of_nonneg_right hQ)⟩, ?_⟩, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).2
    intro i
    have hi : u i ^ 2 ≤ Q := Finset.single_le_sum (fun k _ => sq_nonneg (u k)) (Finset.mem_univ i)
    have habs : |u i| ≤ Real.sqrt (e + Q) := by
      have hh := sq_abs (u i)
      nlinarith [abs_nonneg (u i)]
    change |u i / Real.sqrt (e + Q)| ≤ 1
    rw [abs_div, abs_of_pos hs]
    exact (div_le_one hs).2 habs
  · change e / (e + Q) + ∑ i, (u i / Real.sqrt (e + Q)) ^ 2 = 1
    rw [hsum, ← add_div, div_self hE.ne']

theorem exists_isotropic_first_physical_denominator_margin {N : ℕ} (hN : 0 < N)
    {α : ℝ} (hα : 0 < α) (hhalf : α < Real.pi / 2) (σ : ℂ)
    (hres : σ * Complex.exp (-((N : ℂ) * ((α : ℂ) * Complex.I))) = 1) :
    ∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧ ∀ e : ℝ, 0 < e →
      ∀ u : Fin N → ℝ, (∑ i, u i) = 0 → e + ∑ i, u i ^ 2 < δ →
      c * (e + ∑ i, u i ^ 2) ≤
        ‖isotropicFirstDenominator α σ
          (isotropicRadialParameter α e - (2 * Real.cos α : ℂ), fun i => (u i : ℂ))‖ := by
  obtain ⟨d, c, hd, hc, hmargin⟩ := exists_uniform_isotropic_first_direction_margin hN hα hhalf
  refine ⟨d ^ 2, c, sq_pos_of_pos hd, hc, ?_⟩
  intro e he u hu hsmall
  let Q := ∑ i, u i ^ 2
  let s := Real.sqrt (e + Q)
  let weight := e / (e + Q)
  let x : Fin N → ℝ := fun i => u i / s
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hE : 0 < e + Q := add_pos_of_pos_of_nonneg he hQ
  have hs : 0 < s := Real.sqrt_pos.2 hE
  have hs2 : s ^ 2 = e + Q := Real.sq_sqrt hE.le
  have hsw : s ^ 2 * weight = e := by dsimp only [weight]; rw [hs2]; field_simp
  have hsd : |s| < d := by rw [abs_of_pos hs]; nlinarith
  have hxsum : (∑ i, (x i : ℂ)) = 0 := by
    simp only [x, Complex.ofReal_div, ← Finset.sum_div, ← Complex.ofReal_sum, hu,
      Complex.ofReal_zero, zero_div]
  have hsc (i : Fin N) : (s : ℂ) * (x i : ℂ) = (u i : ℂ) := by
    have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    dsimp only [x]
    rw [Complex.ofReal_div]
    field_simp
  have hπ : α < Real.pi := hhalf.trans (by linarith [Real.pi_pos])
  have hexact := isotropicRadialFilledDenominator_exact hα hπ σ hres
    (fun i => (x i : ℂ)) hxsum s weight (by rw [hsw]; linarith)
  simp only [hsw, hsc] at hexact
  have hm := hmargin s hsd (weight, x) (isotropic_first_normalized_direction he u)
  change c ≤ ‖isotropicRadialFilledDenominator α (fun i => (x i : ℂ))
    (weight : ℂ) (s : ℂ)‖ at hm
  rw [hexact, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, hs2]
  calc
    c * (e + ∑ i, u i ^ 2) = (e + Q) * c := by dsimp only [Q]; ring
    _ ≤ (e + Q) * ‖isotropicRadialFilledDenominator α (fun i => (x i : ℂ))
      (weight : ℂ) (s : ℂ)‖ := mul_le_mul_of_nonneg_left hm hE.le

end
end IsingBulk.AnisoF002.Isotropic
