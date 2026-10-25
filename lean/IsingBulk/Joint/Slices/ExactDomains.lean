import IsingBulk.Joint.Geometry.Definitions
import IsingBulk.Anisotropic.Geometry.Profiles

namespace IsingBulk.Joint
noncomputable section
open IsingBulk.Anisotropic

@[simp] theorem S_ratioSlice (lam : ℝ) (z : ℂ) : S (ratioSlice lam z) = spectralS z := rfl
@[simp] theorem T_ratioSlice (lam : ℝ) (z : ℂ) : T (ratioSlice lam z) = spectralT lam z := rfl
@[simp] theorem A_ratioSlice (lam : ℝ) (z : ℂ) : A (ratioSlice lam z) = spectralA lam z := rfl
@[simp] theorem p_ratioSlice (lam : ℝ) (z : ℂ) : p (ratioSlice lam z) = spectralProduct lam z := rfl

theorem spectralSet_pullback (lam : ℝ) :
    ratioSlice lam ⁻¹' Joint.spectralSet = Anisotropic.spectralSet lam := rfl

theorem slice_strip_iff {lam : ℝ} (hlam : 0 < lam) (y : ℝ) :
    (|y| < Real.pi / 2 ∧ |lam * y| < Real.pi / 2) ↔ |y| < sliceY lam := by
  rw [abs_mul, abs_of_pos hlam]
  unfold sliceY
  by_cases h : lam ≤ 1
  · rw [max_eq_left h, mul_one]
    constructor
    · exact fun hh => hh.1
    · intro hy
      exact ⟨hy, lt_of_le_of_lt (mul_le_of_le_one_left (abs_nonneg y) h) hy⟩
  · have h' : 1 ≤ lam := le_of_lt (lt_of_not_ge h)
    rw [max_eq_right h']
    have he : |y| < Real.pi / (2 * lam) ↔ |y| * (2 * lam) < Real.pi :=
      lt_div_iff₀ (by positivity)
    rw [he]
    constructor
    · intro hh
      nlinarith [hh.2]
    · intro hh
      have hy : lam * |y| < Real.pi / 2 := by nlinarith
      exact ⟨lt_of_le_of_lt (le_mul_of_one_le_left (abs_nonneg y) h') hy, hy⟩

theorem lowDomain_pullback {lam : ℝ} (hlam : 0 < lam) :
    ratioSlice lam ⁻¹' lowDomain = omegaL lam := by
  ext z
  simp only [Set.mem_preimage, lowDomain, ratioSlice, Set.mem_ofPred_eq,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, add_zero]
  change (0 < z.re ∧ 0 < lam * z.re ∧
    |Real.cos z.im| < sliceP lam z.re ∧
    |Real.cos (lam * z.im)| < sliceQ lam z.re) ↔ z ∈ omegaL lam
  have hp : |Real.cos z.im| < sliceP lam z.re ↔
      slicePInv lam |Real.cos z.im| < z.re := by
    conv_rhs => rw [← (sliceP_strictMono hlam).lt_iff_lt]
    rw [sliceP_apply_inv hlam]
  have hq : |Real.cos (lam * z.im)| < sliceQ lam z.re ↔
      sliceQInv lam |Real.cos (lam * z.im)| < z.re := by
    conv_rhs => rw [← (sliceQ_strictMono hlam).lt_iff_lt]
    rw [sliceQ_apply_inv hlam]
  rw [hp, hq]
  constructor
  · intro hz
    exact max_lt hz.2.2.1 hz.2.2.2
  · intro hz
    have hx := omegaL_re_pos hlam hz
    exact ⟨hx, mul_pos hlam hx, (max_lt_iff.mp hz).1, (max_lt_iff.mp hz).2⟩

/-- Exact high-temperature pullback, including the two independent strip conditions. -/
theorem highDomain_pullback {lam : ℝ} (hlam : 0 < lam) :
    ratioSlice lam ⁻¹' highDomain = omegaH lam := by
  ext z
  simp only [Set.mem_preimage, highDomain, ratioSlice, Set.mem_ofPred_eq,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, add_zero]
  have hc : Real.cosh z.re = Real.cosh |z.re| := by
    rcases le_total 0 z.re with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, Real.cosh_neg]
  have hcl : Real.cosh (lam * z.re) = Real.cosh (lam * |z.re|) := by
    rcases le_total 0 z.re with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, mul_neg, Real.cosh_neg]
  simp only [abs_mul, abs_of_pos hlam, hc, hcl]
  change (|z.im| < Real.pi / 2 ∧ lam * |z.im| < Real.pi / 2 ∧
    sliceP lam |z.re| < Real.cos z.im ∧
    sliceQ lam |z.re| < Real.cos (lam * z.im)) ↔
    (|z.im| < sliceY lam ∧ |z.re| < sliceH lam z.im)
  have hp : sliceP lam |z.re| < Real.cos z.im ↔
      |z.re| < slicePInv lam (Real.cos z.im) := by
    conv_rhs => rw [← (sliceP_strictMono hlam).lt_iff_lt]
    rw [sliceP_apply_inv hlam]
  have hq : sliceQ lam |z.re| < Real.cos (lam * z.im) ↔
      |z.re| < sliceQInv lam (Real.cos (lam * z.im)) := by
    conv_rhs => rw [← (sliceQ_strictMono hlam).lt_iff_lt]
    rw [sliceQ_apply_inv hlam]
  have hs := slice_strip_iff hlam z.im
  rw [abs_mul, abs_of_pos hlam] at hs
  rw [hp, hq, sliceH, lt_min_iff]
  constructor
  · rintro ⟨hy, hly, hp, hq⟩
    exact ⟨hs.mp ⟨hy, hly⟩, hp, hq⟩
  · rintro ⟨hy, hp, hq⟩
    obtain ⟨hy, hly⟩ := hs.mpr hy
    exact ⟨hy, hly, hp, hq⟩

end
end IsingBulk.Joint
