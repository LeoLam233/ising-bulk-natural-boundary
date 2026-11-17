import IsingBulk.AnisoF002.Geometry.CanonicalRootContinuity
import IsingBulk.AnisoF002.RegularTail.SchurContraction

/-!
# The literal F002 canceled anisotropic pair

This file proves the subtraction identity behind frozen/published
`eq:cancelpair` directly from the two unsquared dispersion polynomials.
The extended kernel has no reciprocal-angular denominator and is analytic
in the actual spectral parameter off the spectral set when S is nonzero.
No historical Schur, Pfaffian, FIRST, or tail theorem is imported.
-/

namespace IsingBulk.AnisoF002.RegularTail
noncomputable section
open IsingBulk.Anisotropic IsingBulk.AnisoF002.Geometry

def canceledPair (B r s y v : ℂ) : ℂ :=
  -B * (y - v) ^ 2 * r * s / (y * v * (1 - r * s) ^ 2)

theorem dispersion_pair_subtraction {S T A r s y v : ℂ}
    (hr : S * y * (r ^ 2 + 1) - 2 * A * y * r + T * (y ^ 2 + 1) * r = 0)
    (hs : S * v * (s ^ 2 + 1) - 2 * A * v * s + T * (v ^ 2 + 1) * s = 0) :
    S * y * v * (r - s) * (1 - r * s) =
      -T * (y - v) * (1 - y * v) * r * s := by
  linear_combination -s * v * hr + r * y * hs

/-- The algebraic identity is valid without dividing by either root or their
difference. The only angular exclusion is the original Schur denominator. -/
theorem schur_pair_eq_canceled {S T A r s y v : ℂ}
    (hS : S ≠ 0) (hy : y ≠ 0) (hv : v ≠ 0)
    (hroot : 1 - r * s ≠ 0) (hangle : 1 - y * v ≠ 0)
    (hr : S * y * (r ^ 2 + 1) - 2 * A * y * r + T * (y ^ 2 + 1) * r = 0)
    (hs : S * v * (s ^ 2 + 1) - 2 * A * v * s + T * (v ^ 2 + 1) * s = 0) :
    schur r s * schur y v = canceledPair (T / S) r s y v := by
  have h := dispersion_pair_subtraction hr hs
  unfold schur canceledPair
  field_simp
  linear_combination (y - v) * h

theorem pair_root_denominator_ne_zero {r s : ℂ} (hr : ‖r‖ < 1) (hs : ‖s‖ < 1) :
    1 - r * s ≠ 0 := by
  intro he
  have hn := congrArg norm (sub_eq_zero.mp he)
  simp only [norm_mul, norm_one] at hn
  have hlt : ‖r‖ * ‖s‖ < 1 :=
    (mul_le_mul_of_nonneg_left hs.le (norm_nonneg r)).trans_lt (by simpa using hr)
  linarith

theorem exp_angle_dispersion {lam : ℝ} {z : ℂ} (q : ℝ)
    (hz : z ∉ spectralSetF002 lam) :
    spectralS z * Complex.exp ((q : ℂ) * Complex.I) *
        ((spectralSmallRootF002 lam z q) ^ 2 + 1) -
      2 * spectralA lam z * Complex.exp ((q : ℂ) * Complex.I) * spectralSmallRootF002 lam z q +
      spectralT lam z * ((Complex.exp ((q : ℂ) * Complex.I)) ^ 2 + 1) *
        spectralSmallRootF002 lam z q = 0 := by
  have hp := (spectralSmallRootF002_spec q hz).1
  have hc : 2 * (Real.cos q : ℂ) * Complex.exp ((q : ℂ) * Complex.I) =
      (Complex.exp ((q : ℂ) * Complex.I)) ^ 2 + 1 := by
    rw [Complex.ofReal_cos, Complex.two_cos, add_mul]
    have he : Complex.exp (-(q : ℂ) * Complex.I) *
        Complex.exp ((q : ℂ) * Complex.I) = 1 := by
      rw [← Complex.exp_add, neg_mul, neg_add_cancel, Complex.exp_zero]
    rw [he, ← pow_two]
  unfold spectralRootPolynomialF002 at hp
  linear_combination Complex.exp ((q : ℂ) * Complex.I) * hp -
    spectralT lam z * spectralSmallRootF002 lam z q * hc

def spectralCanceledPairF002 (lam : ℝ) (z : ℂ) (q t : ℝ) : ℂ :=
  canceledPair (spectralT lam z / spectralS z)
    (spectralSmallRootF002 lam z q) (spectralSmallRootF002 lam z t)
    (Complex.exp ((q : ℂ) * Complex.I)) (Complex.exp ((t : ℂ) * Complex.I))

theorem spectral_schur_pair_eq_canceled {lam : ℝ} {z : ℂ} (q t : ℝ)
    (hz : z ∉ spectralSetF002 lam) (hS : spectralS z ≠ 0)
    (hangle : 1 - Complex.exp ((q : ℂ) * Complex.I) *
      Complex.exp ((t : ℂ) * Complex.I) ≠ 0) :
    schur (spectralSmallRootF002 lam z q) (spectralSmallRootF002 lam z t) *
      schur (Complex.exp ((q : ℂ) * Complex.I)) (Complex.exp ((t : ℂ) * Complex.I)) =
      spectralCanceledPairF002 lam z q t := by
  exact schur_pair_eq_canceled hS (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
    (pair_root_denominator_ne_zero (spectralSmallRootF002_spec q hz).2
      (spectralSmallRootF002_spec t hz).2) hangle
    (exp_angle_dispersion q hz) (exp_angle_dispersion t hz)

/-- The actual extended pair is analytic at reciprocal-angle collisions too:
there is no assumption excluding `exp(iq) * exp(it) = 1`. -/
theorem spectralCanceledPairF002_analyticAt {lam : ℝ} {z : ℂ} (q t : ℝ)
    (hz : z ∉ spectralSetF002 lam) (hS : spectralS z ≠ 0) :
    AnalyticAt ℂ (fun w => spectralCanceledPairF002 lam w q t) z := by
  have hSr : AnalyticAt ℂ spectralS z := by
    change AnalyticAt ℂ Complex.sinh z
    exact Complex.analyticAt_sinh
  have hTr : AnalyticAt ℂ (spectralT lam) z := by
    change AnalyticAt ℂ (fun w : ℂ => Complex.sinh ((lam : ℂ) * w)) z
    exact Complex.analyticAt_sinh.comp (analyticAt_const.mul analyticAt_id)
  have hq := spectralSmallRootF002_analyticAt q hz
  have ht := spectralSmallRootF002_analyticAt t hz
  have hd := pair_root_denominator_ne_zero (spectralSmallRootF002_spec q hz).2
    (spectralSmallRootF002_spec t hz).2
  unfold spectralCanceledPairF002 canceledPair
  apply (((hTr.div hSr hS).neg.mul analyticAt_const).mul hq).mul ht |>.div
    (analyticAt_const.mul ((analyticAt_const.sub (hq.mul ht)).pow 2))
  exact mul_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _))
    (pow_ne_zero _ hd)

end
end IsingBulk.AnisoF002.RegularTail
