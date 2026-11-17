import IsingBulk.AnisoF002.C03.RegularEdgePhaseJets
import IsingBulk.AnisoF002.Geometry.EndpointBridge
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Constructed inward attenuation on the complete regular-edge real cycle

This is the positive endpoint coordinate of the frozen proof:
`W(q,u)=b+u+a(u)(1-cos(q))`, `u=i*epsilon`.  Positivity of the
imaginary coefficient is obtained on a neighborhood by continuity.  A
compact bound for the genuine logarithmic phase turns the exact cosh
identity into a uniform lower bound by epsilon plus squared angular
distance on the principal real representatives.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set Filter IsingBulk.AnisoF002.Geometry
open scoped Topology BigOperators

theorem sinh_le_mul_exp (x : ℝ) : Real.sinh x ≤ x * Real.exp x := by
  have h := Real.one_sub_le_exp_neg (2 * x)
  have hmul := mul_le_mul_of_nonneg_left (show 1 - Real.exp (-(2 * x)) ≤ 2 * x by linarith)
    (Real.exp_pos x).le
  have he : Real.exp x * Real.exp (-(2 * x)) = Real.exp (-x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [mul_sub, mul_one, he] at hmul
  rw [Real.sinh_eq]
  nlinarith

theorem upperEdgePhase_re_ge_im_div_exp {W : ℂ} {L : ℝ}
    (hW : 0 < W.im) (hL : ‖upperEdgePhase W‖ ≤ L) :
    W.im / Real.exp L ≤ (upperEdgePhase W).re := by
  have hpos := upperEdgePhase_re_pos hW
  have hle := (Complex.re_le_norm (upperEdgePhase W)).trans hL
  have he := Real.exp_le_exp.mpr hle
  have him := congrArg Complex.im (upperEdgePhase_cosh W)
  rw [complex_cosh_im] at him
  have hs := Real.sinh_nonneg_iff.mpr hpos.le
  have hsin := mul_le_mul_of_nonneg_left (Real.sin_le_one (upperEdgePhase W).im) hs
  have hupper : W.im ≤ (upperEdgePhase W).re * Real.exp L := by
    calc
      W.im = Real.sinh (upperEdgePhase W).re * Real.sin (upperEdgePhase W).im := him.symm
      _ ≤ Real.sinh (upperEdgePhase W).re := by simpa only [mul_one] using hsin
      _ ≤ (upperEdgePhase W).re * Real.exp (upperEdgePhase W).re := sinh_le_mul_exp _
      _ ≤ (upperEdgePhase W).re * Real.exp L := mul_le_mul_of_nonneg_left he hpos.le
  exact (div_le_iff₀ (Real.exp_pos L)).mpr hupper

def affineEdgeCenter (b : ℝ) (t : ℂ) : ℂ := (b : ℂ) + t

theorem affineEdgeCenter_analytic (b : ℝ) : AnalyticAt ℂ (affineEdgeCenter b) 0 :=
  analyticAt_const.add analyticAt_id

theorem inward_parameter_norm {eps : ℝ} (he : 0 ≤ eps) :
    ‖(eps : ℂ) * Complex.I‖ = eps := by
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg he]

theorem inward_dispersion_im (b : ℝ) (a : ℂ → ℂ) (eps q : ℝ) :
    (affineEdgeCenter b ((eps : ℂ) * Complex.I) +
      a ((eps : ℂ) * Complex.I) * (1 - (Real.cos q : ℂ))).im =
      eps + (a ((eps : ℂ) * Complex.I)).im * (1 - Real.cos q) := by
  simp [affineEdgeCenter, -Complex.ofReal_cos]

/-- The inward bound is constructed from the regular-edge coefficient;
it is not an added attenuation or physical-model premise.  The same phase
control has a fixed disk before any angular tuple or particle count. -/
theorem exists_regular_edge_inward_attenuation {a : ℂ → ℂ} {b : ℝ}
    (ha : AnalyticAt ℂ a 0) (hb : |b| < 1) (ha0 : 0 < (a 0).im) :
    ∃ d : RegularEdgePhaseControl (affineEdgeCenter b) a,
      ∃ eps0 kappa : ℝ, 0 < eps0 ∧ 0 < kappa ∧
        ∀ eps : ℝ, 0 < eps → eps ≤ eps0 →
          ((eps : ℂ) * Complex.I ∈ Metric.closedBall (0 : ℂ) (d.radius / 4) ∧
            ∀ q : ℝ, |q| ≤ Real.pi →
              kappa * (eps + q ^ 2) ≤
                (edgeAnglePhase (affineEdgeCenter b) a ((eps : ℂ) * Complex.I) q).re) := by
  obtain ⟨d⟩ := exists_regular_edge_phase_control (affineEdgeCenter_analytic b) ha
    (by simp [affineEdgeCenter]) hb ha0
  have hcoeff : ∀ᶠ t : ℂ in 𝓝 0, (a 0).im / 2 < (a t).im :=
    (Complex.continuous_im.continuousAt.comp ha.continuousAt).eventually
      (Ioi_mem_nhds (half_lt_self ha0))
  obtain ⟨r, hr, hcoeffr⟩ := Metric.eventually_nhds_iff.mp hcoeff
  let eps0 : ℝ := min (r / 2) (d.radius / 4)
  let alpha : ℝ := min 1 ((a 0).im / Real.pi ^ 2)
  let kappa : ℝ := alpha / Real.exp d.phaseBound
  have heps0 : 0 < eps0 := lt_min (half_pos hr) (div_pos d.radius_pos (by norm_num))
  have halpha : 0 < alpha := lt_min (by norm_num)
    (div_pos ha0 (sq_pos_of_pos Real.pi_pos))
  have hkappa : 0 < kappa := div_pos halpha (Real.exp_pos _)
  refine ⟨d, eps0, kappa, heps0, hkappa, ?_⟩
  intro eps he he0
  have hte : (eps : ℂ) * Complex.I ∈ Metric.closedBall (0 : ℂ) (d.radius / 4) := by
    rw [Metric.mem_closedBall, dist_zero_right, inward_parameter_norm he.le]
    exact he0.trans (min_le_right _ _)
  refine ⟨hte, ?_⟩
  intro q hq
  have htr : dist ((eps : ℂ) * Complex.I) 0 < r := by
    rw [dist_zero_right, inward_parameter_norm he.le]
    exact (he0.trans (min_le_left _ _)).trans_lt (half_lt_self hr)
  have hamin := (hcoeffr htr).le
  have haeps : 0 < (a ((eps : ℂ) * Complex.I)).im := lt_of_lt_of_le (half_pos ha0) hamin
  have hcos : 0 ≤ 1 - Real.cos q := sub_nonneg.mpr (Real.cos_le_one q)
  have hW : 0 < (affineEdgeCenter b ((eps : ℂ) * Complex.I) +
      a ((eps : ℂ) * Complex.I) * (1 - (Real.cos q : ℂ))).im := by
    rw [inward_dispersion_im]
    exact add_pos_of_pos_of_nonneg he (mul_nonneg haeps.le hcos)
  have hbound := d.phase_bound ((eps : ℂ) * Complex.I)
    (Metric.closedBall_subset_closedBall (by linarith [d.radius_pos]) hte) q
  have hphase := upperEdgePhase_re_ge_im_div_exp hW hbound
  have hcosquad : 2 / Real.pi ^ 2 * q ^ 2 ≤ 1 - Real.cos q := by
    linarith [Real.cos_le_one_sub_mul_cos_sq hq]
  have himlower : alpha * (eps + q ^ 2) ≤
      eps + (a ((eps : ℂ) * Complex.I)).im * (1 - Real.cos q) := by
    have hcprod := mul_le_mul_of_nonneg_left hcosquad (half_pos ha0).le
    have hamul := mul_le_mul_of_nonneg_right hamin hcos
    have ha1 : alpha ≤ 1 := min_le_left _ _
    have haq : alpha ≤ (a 0).im / Real.pi ^ 2 := min_le_right _ _
    have heprod := mul_le_mul_of_nonneg_right ha1 he.le
    have hqprod := mul_le_mul_of_nonneg_right haq (sq_nonneg q)
    have hid : (a 0).im / 2 * (2 / Real.pi ^ 2 * q ^ 2) =
        (a 0).im / Real.pi ^ 2 * q ^ 2 := by ring
    rw [hid] at hcprod
    nlinarith
  calc
    kappa * (eps + q ^ 2) = alpha * (eps + q ^ 2) / Real.exp d.phaseBound := by
      unfold kappa
      ring
    _ ≤ (eps + (a ((eps : ℂ) * Complex.I)).im * (1 - Real.cos q)) /
        Real.exp d.phaseBound := div_le_div_of_nonneg_right himlower (Real.exp_pos _).le
    _ ≤ (edgeAnglePhase (affineEdgeCenter b) a ((eps : ℂ) * Complex.I) q).re := by
      simpa only [inward_dispersion_im, edgeAnglePhase, edgeJointPhase] using hphase

theorem totalPhase_attenuation_of_angle {N : ℕ} {c a : ℂ → ℂ} {t : ℂ}
    {eps kappa : ℝ} (x : Fin N → ℝ)
    (hangle : ∀ i, kappa * (eps + x i ^ 2) ≤ (edgeAnglePhase c a t (x i)).re) :
    kappa * ((N : ℝ) * eps + ∑ i, x i ^ 2) ≤ (edgeTotalPhase c a t x).re := by
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) => hangle i)
  simpa only [Complex.re_sum, ← Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, edgeTotalPhase] using hsum

end
end IsingBulk.AnisoF002.RegularTail.C03
