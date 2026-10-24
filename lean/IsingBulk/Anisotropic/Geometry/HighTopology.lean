import IsingBulk.Anisotropic.Geometry.Profiles
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

namespace IsingBulk.Anisotropic
noncomputable section

theorem sliceY_pos {lam : ℝ} (_hlam : 0 < lam) : 0 < sliceY lam := by
  unfold sliceY
  positivity

theorem central_strip_bounds {lam y : ℝ} (hlam : 0 < lam) (hy : |y| < sliceY lam) :
    |y| < Real.pi/2 ∧ |lam*y| < Real.pi/2 := by
  have hm : 0 < max 1 lam := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have h := (lt_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) hm)).mp hy
  have h1 := le_max_left (1:ℝ) lam
  have h2 := le_max_right (1:ℝ) lam
  rw [abs_mul, abs_of_pos hlam]
  constructor <;> nlinarith [mul_nonneg (abs_nonneg y) (sub_nonneg.mpr h1),
    mul_nonneg (abs_nonneg y) (sub_nonneg.mpr h2)]

theorem sliceH_pos {lam y : ℝ} (hlam : 0 < lam) (hy : |y| < sliceY lam) : 0 < sliceH lam y := by
  obtain ⟨h1,h2⟩ := central_strip_bounds hlam hy
  have hc1 := Real.cos_pos_of_mem_Ioo (abs_lt.mp h1)
  have hc2 := Real.cos_pos_of_mem_Ioo (abs_lt.mp h2)
  apply lt_min
  · simpa only [slicePInv_zero hlam] using slicePInv_strictMono hlam hc1
  · simpa only [sliceQInv_zero hlam] using sliceQInv_strictMono hlam hc2

theorem cos_scale_ge {y b : ℝ} (hy : |y| ≤ Real.pi) (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    Real.cos y ≤ Real.cos (b*y) := by
  rw [← Real.cos_abs y, ← Real.cos_abs (b*y)]
  apply Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) hy
  rw [abs_mul, abs_of_nonneg hb]
  nlinarith [abs_nonneg y]

theorem sliceH_scale_ge {lam y b : ℝ} (hlam : 0 < lam)
    (hy : |y| < sliceY lam) (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    sliceH lam y ≤ sliceH lam (b*y) := by
  obtain ⟨h1,h2⟩ := central_strip_bounds hlam hy
  apply min_le_min
  · exact (slicePInv_strictMono hlam).monotone
      (cos_scale_ge (by linarith [Real.pi_pos]) hb hb1)
  · have hcos := cos_scale_ge (y := lam*y) (by linarith [Real.pi_pos] : |lam*y| ≤ Real.pi) hb hb1
    rw [show b*(lam*y) = lam*(b*y) by ring] at hcos
    exact (sliceQInv_strictMono hlam).monotone hcos

theorem zero_mem_omegaH {lam : ℝ} (hlam : 0 < lam) : (0:ℂ) ∈ omegaH lam := by
  have hy : |(0:ℝ)| < sliceY lam := by simpa using sliceY_pos hlam
  exact ⟨hy, by simpa using sliceH_pos hlam hy⟩

theorem omegaH_starConvex {lam : ℝ} (hlam : 0 < lam) : StarConvex ℝ (0:ℂ) (omegaH lam) := by
  intro z hz a b ha hb hab
  have hb1 : b ≤ 1 := by linarith
  rcases hz with ⟨hy,hx⟩
  have hH := sliceH_scale_ge hlam hy hb hb1
  have hyb : |b*z.im| < sliceY lam := by
    rw [abs_mul, abs_of_nonneg hb]
    nlinarith [abs_nonneg z.im]
  have hxb : |b*z.re| < sliceH lam (b*z.im) := by
    rw [abs_mul, abs_of_nonneg hb]
    have : b*|z.re| ≤ |z.re| := by nlinarith [abs_nonneg z.re]
    exact lt_of_le_of_lt this (lt_of_lt_of_le hx hH)
  simpa only [smul_zero, zero_add, omegaH, Set.mem_ofPred_eq, Complex.smul_im,
    Complex.smul_re, smul_eq_mul] using And.intro hyb hxb

theorem omegaH_isSimplyConnected {lam : ℝ} (hlam : 0 < lam) :
    IsSimplyConnected (omegaH lam) := by
  let : ContractibleSpace (omegaH lam) := (omegaH_starConvex hlam).contractibleSpace ⟨0, zero_mem_omegaH hlam⟩
  change SimplyConnectedSpace _
  infer_instance

end
end IsingBulk.Anisotropic
