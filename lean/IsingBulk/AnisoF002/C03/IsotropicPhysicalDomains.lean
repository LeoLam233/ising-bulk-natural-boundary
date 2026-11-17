import IsingBulk.AnisoF002.C03.IsotropicPhysicalParameter
import IsingBulk.AnisoF002.C03.PhysicalBranchExtension
import IsingBulk.AnisoF002.C03.NegativePhysicalChart

/-!
# The exact original isotropic domains in the physical sinh coordinate

The coordinate is s=sinh z. The HT lens is the unit-disk preimage in
the original central strip; LT is the right-half-plane component of
the exterior preimage. Their complete finite frontiers retain every
height and both HT tips. All identities unfold the original profiles.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open IsingBulk.Anisotropic IsingBulk.AnisoF002.Geometry
open Set Filter

theorem isotropic_profileP (x : ℝ) : profilePF002 1 x = Real.sinh x := by
  simp only [profilePF002, one_mul, Real.tanh_eq_sinh_div_cosh]
  field_simp [ne_of_gt (Real.cosh_pos x)]

theorem isotropic_profileQInv (u : ℝ) : profileQInvF002 1 u = profilePInvF002 1 u := by
  unfold profileQInvF002 profilePInvF002
  congr 1
  funext x
  simp only [profileQF002, profilePF002, one_mul]

theorem isotropic_highProfile_sinh (y : ℝ) :
    Real.sinh (highProfileF002 1 y) = Real.cos y := by
  rw [highProfileF002, one_mul, isotropic_profileQInv, min_self]
  simpa only [isotropic_profileP] using profileP_rightInverse (by norm_num : (0 : ℝ) < 1) (Real.cos y)

theorem isotropic_lowProfile_sinh (y : ℝ) :
    Real.sinh (lowProfileF002 1 y) = |Real.cos y| := by
  rw [lowProfileF002, one_mul, isotropic_profileQInv, max_self]
  simpa only [isotropic_profileP] using profileP_rightInverse (by norm_num : (0 : ℝ) < 1) |Real.cos y|

theorem isotropic_strip_width : highStripWidthF002 1 = Real.pi / 2 := by
  simp only [highStripWidthF002, max_self, mul_one]

theorem isotropic_sinh_norm_square (z : ℂ) :
    ‖Complex.sinh z‖ ^ 2 = Real.sinh z.re ^ 2 + Real.sin z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, complex_sinh_re, complex_sinh_im]
  linear_combination Real.sinh z.re ^ 2 * Real.cos_sq_add_sin_sq z.im +
    Real.sin z.im ^ 2 * Real.cosh_sq_sub_sinh_sq z.re

theorem isotropic_sinh_norm_lt_one (z : ℂ) :
    ‖Complex.sinh z‖ < 1 ↔ |Real.sinh z.re| < |Real.cos z.im| := by
  have hn := isotropic_sinh_norm_square z
  have ht := Real.cos_sq_add_sin_sq z.im
  have ha := sq_abs (Real.sinh z.re)
  have hb := sq_abs (Real.cos z.im)
  have hnorm := norm_nonneg (Complex.sinh z)
  have hs := abs_nonneg (Real.sinh z.re)
  have hc := abs_nonneg (Real.cos z.im)
  constructor <;> intro h <;> nlinarith only [hn, ht, ha, hb, hnorm, hs, hc, h]

theorem isotropic_sinh_norm_gt_one (z : ℂ) :
    1 < ‖Complex.sinh z‖ ↔ |Real.cos z.im| < |Real.sinh z.re| := by
  have hn := isotropic_sinh_norm_square z
  have ht := Real.cos_sq_add_sin_sq z.im
  have ha := sq_abs (Real.sinh z.re)
  have hb := sq_abs (Real.cos z.im)
  have hnorm := norm_nonneg (Complex.sinh z)
  have hs := abs_nonneg (Real.sinh z.re)
  have hc := abs_nonneg (Real.cos z.im)
  constructor <;> intro h <;> nlinarith only [hn, ht, ha, hb, hnorm, hs, hc, h]

theorem isotropic_sinh_norm_eq_one (z : ℂ) :
    ‖Complex.sinh z‖ = 1 ↔ |Real.sinh z.re| = |Real.cos z.im| := by
  have hn := isotropic_sinh_norm_square z
  have ht := Real.cos_sq_add_sin_sq z.im
  have ha := sq_abs (Real.sinh z.re)
  have hb := sq_abs (Real.cos z.im)
  have hnorm := norm_nonneg (Complex.sinh z)
  have hs := abs_nonneg (Real.sinh z.re)
  have hc := abs_nonneg (Real.cos z.im)
  constructor <;> intro h <;> nlinarith only [hn, ht, ha, hb, hnorm, hs, hc, h]

theorem isotropic_high_domain_iff (z : ℂ) :
    z ∈ omegaH 1 ↔ |z.im| < Real.pi / 2 ∧ ‖Complex.sinh z‖ < 1 := by
  change (|z.im| < highStripWidthF002 1 ∧ |z.re| < highProfileF002 1 z.im) ↔ _
  rw [isotropic_strip_width]
  constructor
  · rintro ⟨hy, hx⟩
    have hc := (high_strip_cosines_pos (by norm_num : (0 : ℝ) < 1)
      (by simpa only [isotropic_strip_width] using hy)).1
    refine ⟨hy, (isotropic_sinh_norm_lt_one z).mpr ?_⟩
    rw [abs_of_pos hc, Real.abs_sinh, ← isotropic_highProfile_sinh]
    exact Real.sinh_strictMono hx
  · rintro ⟨hy, hn⟩
    have hc := (high_strip_cosines_pos (by norm_num : (0 : ℝ) < 1)
      (by simpa only [isotropic_strip_width] using hy)).1
    refine ⟨hy, Real.sinh_strictMono.lt_iff_lt.mp ?_⟩
    rw [isotropic_highProfile_sinh, ← Real.abs_sinh, ← abs_of_pos hc]
    exact (isotropic_sinh_norm_lt_one z).mp hn

theorem isotropic_low_domain_iff (z : ℂ) :
    z ∈ omegaL 1 ↔ 0 < z.re ∧ 1 < ‖Complex.sinh z‖ := by
  change lowProfileF002 1 z.im < z.re ↔ _
  constructor
  · intro hx
    have hx0 := lt_of_le_of_lt (lowProfile_nonneg (by norm_num : (0 : ℝ) < 1) z.im) hx
    refine ⟨hx0, (isotropic_sinh_norm_gt_one z).mpr ?_⟩
    rw [abs_of_pos (Real.sinh_pos_iff.mpr hx0), ← isotropic_lowProfile_sinh]
    exact Real.sinh_strictMono hx
  · rintro ⟨hx, hn⟩
    apply Real.sinh_strictMono.lt_iff_lt.mp
    rw [isotropic_lowProfile_sinh]
    have hh := (isotropic_sinh_norm_gt_one z).mp hn
    rwa [abs_of_pos (Real.sinh_pos_iff.mpr hx)] at hh

theorem isotropic_high_frontier_iff (z : ℂ) :
    z ∈ frontier (omegaH 1) ↔ |z.im| ≤ Real.pi / 2 ∧ ‖Complex.sinh z‖ = 1 := by
  change z ∈ frontier (omegaHF002 1) ↔ _
  rw [frontier_omegaHF002 (by norm_num : (0 : ℝ) < 1)]
  change (|z.im| ≤ highStripWidthF002 1 ∧ |z.re| = highProfileF002 1 z.im) ↔ _
  rw [isotropic_strip_width]
  constructor
  · rintro ⟨hy, hx⟩
    refine ⟨hy, (isotropic_sinh_norm_eq_one z).mpr ?_⟩
    rw [Real.abs_sinh, hx, isotropic_highProfile_sinh,
      abs_of_nonneg (Real.cos_nonneg_of_mem_Icc (abs_le.mp hy))]
  · rintro ⟨hy, hn⟩
    refine ⟨hy, Real.sinh_injective ?_⟩
    rw [isotropic_highProfile_sinh, ← Real.abs_sinh]
    have hh := (isotropic_sinh_norm_eq_one z).mp hn
    rwa [abs_of_nonneg (Real.cos_nonneg_of_mem_Icc (abs_le.mp hy))] at hh

theorem isotropic_low_frontier_iff (z : ℂ) :
    z ∈ frontier (omegaL 1) ↔ 0 ≤ z.re ∧ ‖Complex.sinh z‖ = 1 := by
  change z ∈ frontier (omegaLF002 1) ↔ _
  rw [frontier_omegaLF002 (by norm_num : (0 : ℝ) < 1)]
  change lowProfileF002 1 z.im = z.re ↔ _
  constructor
  · intro hx
    have hx0 : 0 ≤ z.re := hx ▸ lowProfile_nonneg (by norm_num : (0 : ℝ) < 1) z.im
    refine ⟨hx0, (isotropic_sinh_norm_eq_one z).mpr ?_⟩
    rw [abs_of_nonneg (Real.sinh_nonneg_iff.mpr hx0), ← hx, isotropic_lowProfile_sinh]
  · rintro ⟨hx, hn⟩
    apply Real.sinh_injective
    rw [isotropic_lowProfile_sinh]
    have hh := (isotropic_sinh_norm_eq_one z).mp hn
    rw [abs_of_nonneg (Real.sinh_nonneg_iff.mpr hx)] at hh
    exact hh.symm

theorem complex_cosh_ne_zero_of_re_ne_zero {z : ℂ} (hx : z.re ≠ 0) : Complex.cosh z ≠ 0 := by
  intro hz
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  rw [complex_cosh_re] at hre
  rw [complex_cosh_im] at him
  have hc : Real.cos z.im = 0 :=
    (mul_eq_zero.mp hre).resolve_left (ne_of_gt (Real.cosh_pos z.re))
  have hs : Real.sin z.im = 0 := (mul_eq_zero.mp him).resolve_left (Real.sinh_ne_zero.mpr hx)
  have hh := Real.cos_sq_add_sin_sq z.im
  rw [hc, hs] at hh
  norm_num at hh

theorem sinh_real_ne_zero_implies_re_ne_zero {z : ℂ} (h : (Complex.sinh z).re ≠ 0) :
    z.re ≠ 0 := by
  intro hz
  rw [complex_sinh_re, hz, Real.sinh_zero, zero_mul] at h
  exact h rfl

end IsingBulk.AnisoF002.Isotropic
