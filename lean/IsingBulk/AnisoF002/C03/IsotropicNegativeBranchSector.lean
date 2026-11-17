import IsingBulk.AnisoF002.C03.IsotropicBranchSector
import IsingBulk.AnisoF002.C03.IsotropicActualAttenuation

/-!
# The negative branch sector and its physical square-root attenuation

On the negative angular side the physical phase sine has a uniformly
large negative imaginary part. The actual cosine normal form, including
its real quadratic error, proves the sector statement. This yields the
physical attenuation needed for the negative-minimum coarea fibers.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology
open Set Metric

theorem sine_negative_sector_of_squared_real_bound (z : ℂ) (hx : 0 ≤ z.re)
    (hy : z.im < 0) (hreal : (z ^ 2).re ≤ ‖z‖ ^ 2 / 20) :
    z.re ≤ (11 / 10 : ℝ) * (-z.im) := by
  have hn : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hs : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by
    simp only [pow_two, Complex.mul_re]
  by_contra hbad
  have hh : 0 < z.re - (11 / 10 : ℝ) * (-z.im) := by linarith only [not_le.mp hbad]
  have hh' : 0 < z.re + (11 / 10 : ℝ) * (-z.im) := by linarith only [hy, hx]
  have hp := mul_pos hh hh'
  nlinarith only [hreal, hn, hs, hp, sq_nonneg z.im]

theorem sine_norm_le_twice_negative_im (z : ℂ) (hx : 0 ≤ z.re) (hy : z.im ≤ 0)
    (hsector : z.re ≤ (11 / 10 : ℝ) * (-z.im)) :
    ‖z‖ ≤ 2 * (-z.im) := by
  have hn : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hs := pow_le_pow_left₀ hx hsector 2
  nlinarith only [hn, hs, hy, norm_nonneg z, sq_nonneg z.im]

theorem exists_isotropic_negative_branch_sine_sector (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ u h : ℝ,
        u ∈ Icc (-r) 0 → h ∈ Icc 0 r →
        let z := Complex.sin (upperPhysicalPhase (isotropicBranchDispersion α b ε u h))
        0 < z.re ∧ z.im < 0 ∧ z.re ≤ (11 / 10 : ℝ) * (-z.im) := by
  obtain ⟨rC, c, C, hrC, hrC1, hc, hC, hnorm⟩ :=
    exists_isotropic_branch_coercivity α b hα hb hpoint
  obtain ⟨rR, M, hrR, hM, hrem⟩ := exists_isotropic_branch_real_remainder α b hα hpoint
  obtain ⟨rA, cA, _, hrA, _, hcA, _, hatten⟩ :=
    exists_isotropic_branch_attenuation α b hα hb
  let K := 2 * M + 3 * C ^ 2
  have hK : 0 < K := by dsimp [K]; positivity
  let r := min rC (min (rR / 2) (min rA (min (1 / (6 * C)) (c / (20 * K)))))
  have hr : 0 < r := by dsimp [r]; positivity
  have hrC' : r ≤ rC := min_le_left _ _
  have hrR' : r ≤ rR / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hrA' : r ≤ rA := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrsmall : r ≤ 1 / (6 * C) := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hrsector : r ≤ c / (20 * K) := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hr1 : r ≤ 1 := hrC'.trans hrC1
  have hCr : 3 * C * r ≤ 1 / 2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 6 * C)).mp hrsmall
    nlinarith only [hh]
  have hKr : K * r ≤ c / 20 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 20 * K)).mp hrsector
    nlinarith only [hh]
  refine ⟨r, hr, hr1, ?_⟩
  intro ε hε hεr u h hu hh
  let W := isotropicBranchDispersion α b ε u h
  let d := 1 - W
  let z := Complex.sin (upperPhysicalPhase W)
  let T := -u + ε + h
  have hT : 0 < T := by dsimp [T]; linarith only [hu.2, hε, hh.1]
  have hTmax : T ≤ 3 * r := by dsimp [T]; linarith only [hu.1, hεr, hh.2]
  have huabs : |u| ≤ r := by rw [abs_of_nonpos hu.2]; linarith only [hu.1]
  obtain ⟨hlo, hhi⟩ := hnorm ε hε (hεr.trans hrC') u h (huabs.trans hrC')
    ⟨hh.1, hh.2.trans hrC'⟩
  rw [abs_of_nonpos hu.2] at hlo hhi
  change c * T ≤ ‖d‖ at hlo
  change ‖d‖ ≤ C * T at hhi
  have hnear : ‖d‖ ≤ 1 / 2 := hhi.trans
    ((mul_le_mul_of_nonneg_left hTmax hC.le).trans (by nlinarith only [hCr]))
  have hWr : 0 < W.re := by
    have hreal := Complex.re_le_norm d
    change 1 - W.re ≤ ‖d‖ at hreal
    linarith only [hreal, hnear]
  have hnormal := isotropic_branch_normal_identity b u h (isotropicRadialParameter α ε)
  change d = _ at hnormal
  have hdi : d.im = -branchAttenuation b (isotropicRadialParameter α ε) u h := by
    rw [hnormal]
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, zero_add, zero_sub]
  have hWi : 0 < W.im := by
    have hβ := (hatten ε hε (hεr.trans hrA') u h (huabs.trans hrA')
      ⟨hh.1, hh.2.trans hrA'⟩).1
    have hp : 0 < cA * (ε + h) := mul_pos hcA (by linarith only [hε, hh.1])
    simp only [d, Complex.sub_im, Complex.one_im, zero_sub] at hdi
    linarith only [hdi, hβ, hp]
  have hzre : 0 < z.re := upperPhysicalPhase_sine_re_pos W hWi
  have hzim : z.im < 0 := upperPhysicalPhase_sine_im_neg W hWi hWr
  refine ⟨hzre, hzim, sine_negative_sector_of_squared_real_bound z hzre.le hzim ?_⟩
  have hR := hrem ε hε (hεr.trans hr1) u h
    ((huabs.trans hrR').trans_lt (half_lt_self hrR))
    (by rw [abs_of_nonneg hh.1]; exact (hh.2.trans hrR').trans_lt (half_lt_self hrR))
  have hqu : u ^ 2 ≤ r * (-u) := by nlinarith only [hu.1, hu.2]
  have hqh : h ^ 2 ≤ r * h := by nlinarith only [hh.1, hh.2]
  have hqε : ε ^ 2 ≤ r * ε := by nlinarith only [hε, hεr]
  have hRbound : |branchRealRemainder b (isotropicRadialParameter α ε) u h| ≤ M * r * T := by
    have hq := mul_le_mul_of_nonneg_left (by dsimp [T]; linarith only [hqu, hqh, hqε] :
      u ^ 2 + h ^ 2 + ε ^ 2 ≤ r * T) hM.le
    exact hR.trans (hq.trans_eq (by ring))
  have hdr : d.re ≤ M * r * T := by
    have hre : d.re = Real.sin b * u + branchRealRemainder b (isotropicRadialParameter α ε) u h := by
      rw [hnormal]
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
    have hsu := mul_nonpos_of_nonneg_of_nonpos (Real.sin_pos_of_pos_of_lt_pi hb.1 hb.2).le hu.2
    linarith only [hre, (abs_le.mp hRbound).2, hsu]
  have hdsq : ‖d‖ ^ 2 ≤ 3 * C ^ 2 * r * T := by
    have hp := pow_le_pow_left₀ (norm_nonneg d) hhi 2
    have hT2 := mul_le_mul_of_nonneg_right hTmax hT.le
    have hcT := mul_le_mul_of_nonneg_left hT2 (sq_nonneg C)
    nlinarith only [hp, hcT]
  have hzsq : z ^ 2 = 2 * d - d ^ 2 := by
    rw [Complex.sin_sq, upperPhysicalPhase_cos]
    dsimp [d]
    ring
  have hsqre : (z ^ 2).re ≤ K * r * T := by
    have hp := (abs_le.mp (Complex.abs_re_le_norm (d ^ 2))).1
    rw [norm_pow] at hp
    rw [hzsq, Complex.sub_re, Complex.mul_re]
    norm_num
    dsimp [K]
    nlinarith only [hdr, hp, hdsq]
  have hplus : 1 ≤ ‖1 + W‖ := (one_add_norm_of_near_one W (by linarith only [hnear])).1
  have hsqnorm : c * T ≤ ‖z‖ ^ 2 := by
    rw [upperPhysicalPhase_sine_norm_sq]
    change c * T ≤ ‖d‖ * ‖1 + W‖
    have hmul : ‖d‖ ≤ ‖d‖ * ‖1 + W‖ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hplus (norm_nonneg d)
    exact hlo.trans hmul
  have hsmall := mul_le_mul_of_nonneg_right hKr hT.le
  nlinarith only [hsqre, hsqnorm, hsmall]

end IsingBulk.AnisoF002.Isotropic
