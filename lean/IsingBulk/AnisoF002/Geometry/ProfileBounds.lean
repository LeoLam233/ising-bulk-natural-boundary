import IsingBulk.AnisoF002.Geometry.ProfileMonotonicity

/-!
# Critical value and the exact physical profile bounds

F002 `eq:physicalPQ`, `eq:Hdef`, `eq:Ldef`, `eq:domains`, and
`thm:components`.  The critical point is constructed from the proved inverse
profile, and the original hyperbolic critical equation is then derived.
The global low-temperature graph is the literal maximum of the two inverse
absolute-cosine profiles; both its continuity and its full uniform bounds
are proved here.
-/

namespace IsingBulk.AnisoF002.Geometry
noncomputable section
open Set

def criticalPointF002 (lam : ℝ) : ℝ := profilePInvF002 lam 1
def highStripWidthF002 (lam : ℝ) : ℝ := Real.pi / (2 * max 1 lam)
def highProfileF002 (lam y : ℝ) : ℝ :=
  min (profilePInvF002 lam (Real.cos y)) (profileQInvF002 lam (Real.cos (lam * y)))
def lowProfileF002 (lam y : ℝ) : ℝ :=
  max (profilePInvF002 lam |Real.cos y|) (profileQInvF002 lam |Real.cos (lam * y)|)
def omegaHF002 (lam : ℝ) : Set ℂ :=
  {z | |z.im| < highStripWidthF002 lam ∧ |z.re| < highProfileF002 lam z.im}
def omegaLF002 (lam : ℝ) : Set ℂ := {z | lowProfileF002 lam z.im < z.re}

theorem profileQ_zero (lam : ℝ) : profileQF002 lam 0 = 0 := by
  simp only [profileQF002, Real.tanh_zero, mul_zero]

theorem profilePInv_zero {lam : ℝ} (hlam : 0 < lam) : profilePInvF002 lam 0 = 0 := by
  simpa only [profileP_zero] using profileP_leftInverse hlam 0

theorem profileQInv_zero {lam : ℝ} (hlam : 0 < lam) : profileQInvF002 lam 0 = 0 := by
  simpa only [profileQ_zero] using profileQ_leftInverse hlam 0

theorem criticalPointF002_pos {lam : ℝ} (hlam : 0 < lam) : 0 < criticalPointF002 lam := by
  have hh := profilePInv_strictMono hlam (show (0 : ℝ) < 1 by norm_num)
  rwa [profilePInv_zero hlam] at hh

theorem profileP_critical {lam : ℝ} (hlam : 0 < lam) :
    profilePF002 lam (criticalPointF002 lam) = 1 := profileP_rightInverse hlam 1

theorem profileP_eq_one_iff_hyperbolic (lam x : ℝ) :
    profilePF002 lam x = 1 ↔ Real.cosh x * Real.sinh (lam * x) = Real.cosh (lam * x) := by
  unfold profilePF002
  rw [Real.tanh_eq_sinh_div_cosh, ← mul_div_assoc,
    div_eq_iff (ne_of_gt (Real.cosh_pos (lam * x))), one_mul]

theorem profileP_eq_one_iff_product {lam x : ℝ} (hlam : 0 < lam) (hx : 0 < x) :
    profilePF002 lam x = 1 ↔ Real.sinh x * Real.sinh (lam * x) = 1 := by
  rw [profileP_eq_one_iff_hyperbolic]
  let h := Real.sinh x
  let c := Real.cosh x
  let H := Real.sinh (lam * x)
  let C := Real.cosh (lam * x)
  have hc : c ^ 2 - h ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq x
  have hC : C ^ 2 - H ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq (lam * x)
  have hh : 0 < h := Real.sinh_pos_iff.mpr hx
  have hH : 0 < H := Real.sinh_pos_iff.mpr (mul_pos hlam hx)
  have hcpos : 0 < c := Real.cosh_pos x
  have hCpos : 0 < C := Real.cosh_pos (lam * x)
  change c * H = C ↔ h * H = 1
  constructor
  · intro hp
    have hp2 := congrArg (fun a : ℝ => a ^ 2) hp
    have hs : (h * H) ^ 2 = 1 := by
      linear_combination hp2 - H ^ 2 * hc + hC
    nlinarith [mul_pos hh hH]
  · intro hp
    have hp2 := congrArg (fun a : ℝ => a ^ 2) hp
    have hs : (c * H) ^ 2 = C ^ 2 := by
      linear_combination H ^ 2 * hc - hC + hp2
    nlinarith [mul_pos hcpos hH]

theorem criticalPointF002_equation {lam : ℝ} (hlam : 0 < lam) :
    Real.sinh (criticalPointF002 lam) * Real.sinh (lam * criticalPointF002 lam) = 1 :=
  (profileP_eq_one_iff_product hlam (criticalPointF002_pos hlam)).mp (profileP_critical hlam)

theorem criticalPointF002_unique {lam x : ℝ} (hlam : 0 < lam) (hx : 0 < x)
    (hp : Real.sinh x * Real.sinh (lam * x) = 1) : x = criticalPointF002 lam := by
  apply (profileP_strictMono hlam).injective
  rw [profileP_critical hlam]
  exact (profileP_eq_one_iff_product hlam hx).mpr hp

theorem profileQ_critical {lam : ℝ} (hlam : 0 < lam) :
    profileQF002 lam (criticalPointF002 lam) = 1 := by
  let x := criticalPointF002 lam
  have hp : Real.cosh x * Real.sinh (lam * x) = Real.cosh (lam * x) :=
    (profileP_eq_one_iff_hyperbolic lam x).mp (profileP_critical hlam)
  have hprod : Real.sinh x * Real.sinh (lam * x) = 1 := criticalPointF002_equation hlam
  change Real.cosh (lam * x) * Real.tanh x = 1
  rw [Real.tanh_eq_sinh_div_cosh, ← mul_div_assoc,
    div_eq_iff (ne_of_gt (Real.cosh_pos x)), one_mul]
  linear_combination -Real.sinh x * hp + Real.cosh x * hprod

theorem profileQInv_one {lam : ℝ} (hlam : 0 < lam) :
    profileQInvF002 lam 1 = criticalPointF002 lam := by
  have hh := profileQ_leftInverse hlam (criticalPointF002 lam)
  rwa [profileQ_critical hlam] at hh

theorem profilePInv_nonneg {lam a : ℝ} (hlam : 0 < lam) (ha : 0 ≤ a) :
    0 ≤ profilePInvF002 lam a := by
  have hh := (profilePInv_strictMono hlam).monotone ha
  rwa [profilePInv_zero hlam] at hh

theorem profileQInv_nonneg {lam a : ℝ} (hlam : 0 < lam) (ha : 0 ≤ a) :
    0 ≤ profileQInvF002 lam a := by
  have hh := (profileQInv_strictMono hlam).monotone ha
  rwa [profileQInv_zero hlam] at hh

theorem highProfile_continuous {lam : ℝ} (hlam : 0 < lam) : Continuous (highProfileF002 lam) := by
  unfold highProfileF002
  exact ((profilePInv_continuous hlam).comp Real.continuous_cos).min
    ((profileQInv_continuous hlam).comp (Real.continuous_cos.comp (continuous_const.mul continuous_id)))

theorem lowProfile_continuous {lam : ℝ} (hlam : 0 < lam) : Continuous (lowProfileF002 lam) := by
  unfold lowProfileF002
  exact ((profilePInv_continuous hlam).comp Real.continuous_cos.abs).max
    ((profileQInv_continuous hlam).comp
      (Real.continuous_cos.comp (continuous_const.mul continuous_id)).abs)

theorem lowProfile_nonneg {lam : ℝ} (hlam : 0 < lam) (y : ℝ) : 0 ≤ lowProfileF002 lam y :=
  (profilePInv_nonneg hlam (abs_nonneg _)).trans (le_max_left _ _)

theorem lowProfile_le_criticalPoint {lam : ℝ} (hlam : 0 < lam) (y : ℝ) :
    lowProfileF002 lam y ≤ criticalPointF002 lam := by
  apply max_le
  · exact (profilePInv_strictMono hlam).monotone (Real.abs_cos_le_one y)
  · have hh := (profileQInv_strictMono hlam).monotone (Real.abs_cos_le_one (lam * y))
    rwa [profileQInv_one hlam] at hh

theorem highProfile_zero {lam : ℝ} (hlam : 0 < lam) :
    highProfileF002 lam 0 = criticalPointF002 lam := by
  simp only [highProfileF002, mul_zero, Real.cos_zero, profileQInv_one hlam, criticalPointF002, min_self]

theorem lowProfile_zero {lam : ℝ} (hlam : 0 < lam) :
    lowProfileF002 lam 0 = criticalPointF002 lam := by
  simp only [lowProfileF002, mul_zero, Real.cos_zero, abs_one, profileQInv_one hlam,
    criticalPointF002, max_self]

theorem real_mem_omegaLF002_iff {lam x : ℝ} (hlam : 0 < lam) :
    (x : ℂ) ∈ omegaLF002 lam ↔ criticalPointF002 lam < x := by
  change lowProfileF002 lam 0 < x ↔ criticalPointF002 lam < x
  rw [lowProfile_zero hlam]

theorem isOpen_omegaLF002 {lam : ℝ} (hlam : 0 < lam) : IsOpen (omegaLF002 lam) :=
  isOpen_lt ((lowProfile_continuous hlam).comp Complex.continuous_im) Complex.continuous_re

end
end IsingBulk.AnisoF002.Geometry
