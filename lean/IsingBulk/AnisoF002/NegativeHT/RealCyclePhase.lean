import IsingBulk.AnisoF002.NegativeHT.WindingScale
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.GCongr

/-!
# Exact curvature and phase cost for the negative-HT real cycle

These are the actual scalar curvature from F002 `eq:rc-h` and the
quantitative comparison underlying `eq:rc-phase-cost`.  The imaginary part
of the curvature is retained.
-/

namespace IsingBulk.AnisoF002.NegativeHT

noncomputable section

/-- Literal first-winding quadratic curvature, with B evaluated at tau_n. -/
def firstWindingCurvature (n : ℕ) (B : ℂ) (b s : ℝ) : ℂ :=
  (Real.cos (Real.pi/(n : ℝ)) : ℂ) -
    B*(b : ℂ)/(s : ℂ)^2*(Real.sin (Real.pi/(n : ℝ)) : ℂ)^2

theorem firstWindingCurvature_norm_sub_one_le (n : ℕ) (B : ℂ) (b s : ℝ) :
    ‖firstWindingCurvature n B b s - 1‖ ≤
      (1+2*‖B‖*|b|/s^2)*windingTau n := by
  let d := Real.pi/(n : ℝ)
  have hτ : 0 ≤ windingTau n := by
    unfold windingTau
    exact sub_nonneg.mpr (Real.cos_le_one _)
  have hsin : (Real.sin d)^2 ≤ 2*windingTau n := by
    have hid := Real.sin_sq_add_cos_sq d
    have hsq := sq_nonneg (1-Real.cos d)
    change (Real.sin d)^2 ≤ 2*(1-Real.cos d)
    nlinarith
  have hc : ‖(Real.cos d : ℂ)-1‖ = windingTau n := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (Real.cos_le_one _))]
    change -(Real.cos d-1) = 1-Real.cos d
    ring
  have hb : ‖B*(b : ℂ)/(s : ℂ)^2*(Real.sin d : ℂ)^2‖ =
      ‖B‖*|b|/s^2*(Real.sin d)^2 := by
    simp only [norm_mul, norm_div, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
  have hcoef : 0 ≤ ‖B‖*|b|/s^2 := by positivity
  change ‖(Real.cos d : ℂ) -
    B*(b : ℂ)/(s : ℂ)^2*(Real.sin d : ℂ)^2 - 1‖ ≤ _
  calc
    _ = ‖((Real.cos d : ℂ)-1) -
        B*(b : ℂ)/(s : ℂ)^2*(Real.sin d : ℂ)^2‖ := by congr 1; ring
    _ ≤ ‖(Real.cos d : ℂ)-1‖ +
        ‖B*(b : ℂ)/(s : ℂ)^2*(Real.sin d : ℂ)^2‖ := norm_sub_le _ _
    _ = windingTau n + ‖B‖*|b|/s^2*(Real.sin d)^2 := by rw [hc, hb]
    _ ≤ windingTau n + (‖B‖*|b|/s^2)*(2*windingTau n) := by
      gcongr
    _ = _ := by ring

/-- A finite uniform curvature estimate at the exact pole centers. -/
theorem firstWindingCurvature_uniform_bound (n : ℕ) (B : ℂ) (b s K : ℝ)
    (hn : 0<n) (hK : ‖B‖≤K) :
    ‖firstWindingCurvature n B b s-1‖ ≤
      (1+2*K*|b|/s^2)*Real.pi^2/(2*(n : ℝ)^2) := by
  have hK0 : 0≤K := (norm_nonneg _).trans hK
  have hc : 0≤1+2*‖B‖*|b|/s^2 := by positivity
  have hd : 1+2*‖B‖*|b|/s^2 ≤ 1+2*K*|b|/s^2 := by gcongr
  have ht := windingTau_bounds n hn
  calc
    _ ≤ (1+2*‖B‖*|b|/s^2)*windingTau n :=
      firstWindingCurvature_norm_sub_one_le n B b s
    _ ≤ (1+2*‖B‖*|b|/s^2)*(Real.pi^2/(2*(n : ℝ)^2)) := by
      exact mul_le_mul_of_nonneg_left ht.2 hc
    _ ≤ (1+2*K*|b|/s^2)*(Real.pi^2/(2*(n : ℝ)^2)) := by gcongr
    _ = _ := by ring

/-- Exact logarithmic phase cost, bounded using only the imaginary part
relative to the positive real part. -/
theorem log_curvature_phase_cost {h : ℂ} (hh : 0 < h.re) :
    0 ≤ Real.log (‖h‖/h.re) ∧
      Real.log (‖h‖/h.re) ≤ h.im^2/(2*h.re^2) := by
  have hh0 : h ≠ 0 := by intro he; simp [he] at hh
  have hr : 0 < ‖h‖/h.re := div_pos (norm_pos_iff.mpr hh0) hh
  have hr1 : 1 ≤ ‖h‖/h.re := (one_le_div hh).mpr (Complex.re_le_norm h)
  have hnorm := Complex.sq_norm_sub_sq_re h
  have he : (‖h‖/h.re)^2-1 = h.im^2/h.re^2 := by
    rw [div_pow]
    apply (eq_div_iff (pow_ne_zero 2 hh.ne')).mpr
    field_simp
    nlinarith
  have hlog := Real.log_le_sub_one_of_pos (pow_pos hr 2)
  rw [Real.log_pow, he] at hlog
  constructor
  · exact Real.log_nonneg hr1
  · norm_num at hlog
    rw [show h.im^2/(2*h.re^2) = (h.im^2/h.re^2)/2 by ring]
    linarith

/-- The full integer-power phase ratio. No common-phase assumption enters. -/
theorem curvature_phase_cost (α : ℕ) {h : ℂ} (hh : 0 < h.re) :
    1 ≤ (‖h‖/h.re)^α ∧
      (‖h‖/h.re)^α ≤ Real.exp ((α : ℝ)*h.im^2/(2*h.re^2)) := by
  have hh0 : h ≠ 0 := by intro he; simp [he] at hh
  have hr : 0 < ‖h‖/h.re := div_pos (norm_pos_iff.mpr hh0) hh
  have hc := log_curvature_phase_cost hh
  constructor
  · exact one_le_pow₀ ((one_le_div hh).mpr (Complex.re_le_norm h))
  · apply (Real.log_le_iff_le_exp (pow_pos hr α)).mp
    rw [Real.log_pow]
    have hm := mul_le_mul_of_nonneg_left hc.2 (show (0 : ℝ)≤α by positivity)
    simpa only [mul_div_assoc] using hm

end

end IsingBulk.AnisoF002.NegativeHT
