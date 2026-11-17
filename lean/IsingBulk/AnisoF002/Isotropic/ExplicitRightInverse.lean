import IsingBulk.AnisoF002.Isotropic.RightArc
import Mathlib.Analysis.RCLike.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# One explicit analytic inverse on the isotropic right arc

The single logarithm/square-root branch below realizes the explicit inverse
in frozen F002 `eq:iso-inverse-explicit`.  It gives compatible values rather
than choosing unrelated local inverses at different real points.  The
original unsquared dispersion identity is proved directly.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open ComplexOrder
open scoped Topology

def rightArcCosArgument (z : ℂ) : ℂ := z + Complex.I * Complex.sqrt (1 - z ^ 2)

def rightArcCos (z : ℂ) : ℂ := -Complex.I * Complex.log (rightArcCosArgument z)

def explicitRightInverse (q : ℂ × ℂ) : ℂ :=
  q.2 / 2 - rightArcCos (q.1 / (2 * Complex.cos (q.2 / 2)))

theorem rightArcCosArgument_product (z : ℂ) :
    rightArcCosArgument z * (z - Complex.I * Complex.sqrt (1 - z ^ 2)) = 1 := by
  have hs : Complex.sqrt (1 - z ^ 2) ^ 2 = 1 - z ^ 2 := by
    simpa only [Complex.sqrt] using Complex.cpow_ofNat_inv_pow (1 - z ^ 2) 2
  unfold rightArcCosArgument
  linear_combination (-(Complex.sqrt (1 - z ^ 2)) ^ 2) * Complex.I_sq + hs

theorem rightArcCosArgument_ne_zero (z : ℂ) : rightArcCosArgument z ≠ 0 := by
  intro h
  have hp := rightArcCosArgument_product z
  rw [h, zero_mul] at hp
  exact zero_ne_one hp

/-- The logarithmic branch satisfies the actual cosine equation. -/
theorem rightArcCos_cos (z : ℂ) : Complex.cos (rightArcCos z) = z := by
  have ht := rightArcCosArgument_ne_zero z
  have hi : (rightArcCosArgument z)⁻¹ = z - Complex.I * Complex.sqrt (1 - z ^ 2) := by
    calc
      (rightArcCosArgument z)⁻¹ = (rightArcCosArgument z)⁻¹ * 1 := by rw [mul_one]
      _ = (rightArcCosArgument z)⁻¹ *
          (rightArcCosArgument z * (z - Complex.I * Complex.sqrt (1 - z ^ 2))) := by
        rw [rightArcCosArgument_product]
      _ = z - Complex.I * Complex.sqrt (1 - z ^ 2) := by
        rw [← mul_assoc, inv_mul_cancel₀ ht, one_mul]
  have hangle : rightArcCos z * Complex.I = Complex.log (rightArcCosArgument z) := by
    unfold rightArcCos
    linear_combination -(Complex.log (rightArcCosArgument z)) * Complex.I_sq
  have hneg : -rightArcCos z * Complex.I = -Complex.log (rightArcCosArgument z) := by
    rw [neg_mul, hangle]
  unfold Complex.cos
  rw [hangle, hneg, Complex.exp_neg, Complex.exp_log ht, hi]
  unfold rightArcCosArgument
  ring

theorem rightArcCos_analyticAt (z : ℂ)
    (hr : 1 - z ^ 2 ∈ Complex.slitPlane)
    (ha : rightArcCosArgument z ∈ Complex.slitPlane) :
    AnalyticAt ℂ rightArcCos z := by
  have hb : AnalyticAt ℂ (fun z : ℂ => 1 - z ^ 2) z :=
    analyticAt_const.sub (analyticAt_id.pow 2)
  have hs : AnalyticAt ℂ (fun z => Complex.sqrt (1 - z ^ 2)) z := by
    simpa only [Complex.sqrt] using
      hb.cpow (g := fun _ : ℂ => (2⁻¹ : ℂ)) analyticAt_const hr
  unfold rightArcCos rightArcCosArgument
  exact analyticAt_const.mul ((analyticAt_id.add (analyticAt_const.mul hs)).clog ha)

theorem rightArcCos_sqrt_ofReal (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) :
    Complex.sqrt (1 - (x : ℂ) ^ 2) = (Real.sqrt (1 - x ^ 2) : ℂ) := by
  have hr : 0 ≤ 1 - x ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx.2) (by linarith [hx.1] : 0 ≤ 1 + x)]
  have hrC : (0 : ℂ) ≤ ((1 - x ^ 2 : ℝ) : ℂ) := by exact_mod_cast hr
  have hs : Complex.sqrt ((1 - x ^ 2 : ℝ) : ℂ) = (Real.sqrt (1 - x ^ 2) : ℂ) := by
    simpa only [Complex.ofReal_re] using Complex.sqrt_of_nonneg hrC
  simpa only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow] using hs

/-- The chosen complex branch agrees with the real physical arccosine. -/
theorem rightArcCos_ofReal (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) :
    rightArcCos x = (Real.arccos x : ℂ) := by
  have he : Complex.exp ((Real.arccos x : ℂ) * Complex.I) = rightArcCosArgument x := by
    unfold rightArcCosArgument
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_arccos (by linarith [hx.1]) hx.2, Real.sin_arccos,
      rightArcCos_sqrt_ofReal x hx]
    ring
  have hlo : -Real.pi < Real.arccos x := by
    linarith [Real.arccos_nonneg x, Real.pi_pos]
  have hl := Complex.log_exp (x := (Real.arccos x : ℂ) * Complex.I)
    (by simpa using hlo) (by simpa using Real.arccos_le_pi x)
  unfold rightArcCos
  rw [← he, hl]
  linear_combination -(Real.arccos x : ℂ) * Complex.I_sq

theorem rightArcCos_analyticAt_ofReal (x : ℝ) (hx : 0 < x ∧ x < 1) :
    AnalyticAt ℂ rightArcCos (x : ℂ) := by
  apply rightArcCos_analyticAt
  · have hr : 0 < 1 - x ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr hx.2) (by linarith [hx.1] : 0 < 1 + x)]
    have hc : (((1 - x ^ 2 : ℝ) : ℂ)) ∈ Complex.slitPlane :=
      Complex.ofReal_mem_slitPlane.mpr hr
    simpa only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow] using hc
  · apply Complex.mem_slitPlane_iff.mpr
    left
    unfold rightArcCosArgument
    rw [rightArcCos_sqrt_ofReal x ⟨hx.1.le, hx.2.le⟩]
    simpa using hx.1

/-- The single explicit right inverse satisfies the original dispersion,
without squaring the relation or weakening to a discriminant equation. -/
theorem explicitRightInverse_dispersion (q : ℂ × ℂ)
    (hc : Complex.cos (q.2 / 2) ≠ 0) :
    Complex.cos (explicitRightInverse q) +
      Complex.cos (q.2 - explicitRightInverse q) = q.1 := by
  rw [Complex.cos_add_cos]
  have hs : (explicitRightInverse q + (q.2 - explicitRightInverse q)) / 2 = q.2 / 2 := by
    ring
  have hd : (explicitRightInverse q - (q.2 - explicitRightInverse q)) / 2 =
      -rightArcCos (q.1 / (2 * Complex.cos (q.2 / 2))) := by
    unfold explicitRightInverse
    ring
  rw [hs, hd, Complex.cos_neg, rightArcCos_cos]
  field_simp

theorem explicitRightInverse_analyticAt (q : ℂ × ℂ)
    (hc : Complex.cos (q.2 / 2) ≠ 0)
    (ha : AnalyticAt ℂ rightArcCos (q.1 / (2 * Complex.cos (q.2 / 2)))) :
    AnalyticAt ℂ explicitRightInverse q := by
  have hh : AnalyticAt ℂ (fun z : ℂ × ℂ => z.2 / 2) q :=
    analyticAt_snd.div analyticAt_const (by norm_num)
  have hr : AnalyticAt ℂ (fun z : ℂ × ℂ => z.1 / (2 * Complex.cos (z.2 / 2))) q :=
    analyticAt_fst.div (analyticAt_const.mul (Complex.analyticAt_cos.comp hh))
      (mul_ne_zero (by norm_num) hc)
  exact hh.sub (ha.comp (f := fun z : ℂ × ℂ => z.1 / (2 * Complex.cos (z.2 / 2))) hr)

/-- The entire real interval used by the right inverse stays inside the
single real arccosine branch, with no endpoint discriminant zero. -/
theorem rightInverseRatio_bounds (S v : ℝ) (hS : 0 < S ∧ S < 2)
    (hv : v ∈ Set.Ioo (-2 * Real.arccos (S / 2)) (2 * Real.arccos (S / 2))) :
    0 < Real.cos (v / 2) ∧
      (0 < S / (2 * Real.cos (v / 2)) ∧ S / (2 * Real.cos (v / 2)) < 1) := by
  have habs : |v / 2| < Real.arccos (S / 2) := by
    rw [abs_lt]
    constructor <;> linarith [hv.1, hv.2]
  have hc := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg (v / 2))
    (Real.arccos_le_pi (S / 2)) habs
  rw [Real.cos_arccos (by linarith [hS.1]) (by linarith [hS.2]), Real.cos_abs] at hc
  have hcos : 0 < Real.cos (v / 2) := by linarith [hS.1]
  refine ⟨hcos, div_pos hS.1 (by positivity), ?_⟩
  apply (div_lt_one (by positivity : 0 < 2 * Real.cos (v / 2))).2
  linarith

theorem rightInverseRatio_complex_cast (S v : ℝ) :
    (S : ℂ) / (2 * Complex.cos ((v : ℂ) / 2)) =
      ((S / (2 * Real.cos (v / 2)) : ℝ) : ℂ) := by
  push_cast
  rfl

/-- One and the same explicit U is jointly analytic at every real point of
the full right interval. -/
theorem explicitRightInverse_analyticAt_real (S v : ℝ) (hS : 0 < S ∧ S < 2)
    (hv : v ∈ Set.Ioo (-2 * Real.arccos (S / 2)) (2 * Real.arccos (S / 2))) :
    AnalyticAt ℂ explicitRightInverse ((S : ℂ), (v : ℂ)) := by
  have hb := rightInverseRatio_bounds S v hS hv
  have hc : Complex.cos ((v : ℂ) / 2) ≠ 0 := by
    have hcR : (Real.cos (v / 2) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt hb.1)
    simpa using hcR
  apply explicitRightInverse_analyticAt ((S : ℂ), (v : ℂ)) hc
  rw [rightInverseRatio_complex_cast]
  exact rightArcCos_analyticAt_ofReal _ hb.2

/-- This fixes the real inverse branch by the actual original pair of
angles, rather than by a squared spectral equation. -/
theorem rightArc_real_arccos_identity (S w : ℝ) (hS : 0 < S ∧ S < 2)
    (hw : w ∈ Set.Icc (-rightBranchEndpoint S) 0) :
    Real.arccos (S / (2 * Real.cos (rightArcCoordinate S w / 2))) =
      (rightArcPhase S w - w) / 2 := by
  have hg := rightArcPhase_range S w hS.1
  have hv := rightArcCoordinate_inside_discriminant_interval S w hS hw
  have hb := rightInverseRatio_bounds S (rightArcCoordinate S w) hS hv
  have hsum : Real.cos w + Real.cos (rightArcPhase S w) = S := by
    rw [rightArcPhase_cos S w hS hw]
    ring
  have ht := Real.cos_add_cos w (rightArcPhase S w)
  rw [hsum, show (w - rightArcPhase S w) / 2 =
    -((rightArcPhase S w - w) / 2) by ring, Real.cos_neg] at ht
  have hcos : Real.cos ((rightArcPhase S w - w) / 2) =
      S / (2 * Real.cos (rightArcCoordinate S w / 2)) := by
    apply (eq_div_iff (ne_of_gt (mul_pos (by norm_num : (0 : ℝ) < 2) hb.1))).2
    change Real.cos ((rightArcPhase S w - w) / 2) *
      (2 * Real.cos ((w + rightArcPhase S w) / 2)) = S
    linear_combination -ht
  rw [← hcos]
  apply Real.arccos_cos
  · linarith [hw.2, hg.1]
  · have hbpi := rightBranchEndpoint_lt_pi S hS.1
    linarith [hw.1, hg.2]

/-- The single explicit complex inverse takes the correct value at every
point of the full physical right arc. -/
theorem explicitRightInverse_on_right_arc (S w : ℝ) (hS : 0 < S ∧ S < 2)
    (hw : w ∈ Set.Icc (-rightBranchEndpoint S) 0) :
    explicitRightInverse ((S : ℂ), (rightArcCoordinate S w : ℂ)) = w := by
  have hb := rightInverseRatio_bounds S (rightArcCoordinate S w) hS
    (rightArcCoordinate_inside_discriminant_interval S w hS hw)
  unfold explicitRightInverse
  rw [rightInverseRatio_complex_cast,
    rightArcCos_ofReal _ ⟨hb.2.1.le, hb.2.2.le⟩,
    rightArc_real_arccos_identity S w hS hw]
  unfold rightArcCoordinate
  push_cast
  ring

end IsingBulk.AnisoF002.Isotropic
