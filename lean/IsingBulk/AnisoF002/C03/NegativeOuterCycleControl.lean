import IsingBulk.AnisoF002.C03.NegativeGlobalAttenuation
import IsingBulk.AnisoF002.C03.NegativeJointRealNumerator
import IsingBulk.AnisoF002.C03.RegularEdgeSiteKernel

/-!
# Actual outer real-cycle density on a uniform inverse-particle disk

The positive real part of the literal phase at temperature zero controls
the whole complement of a fixed angular cutoff.  The disk is c/N, with
c chosen before N.  The complete physical numerator retains its exact
W_N normalization and its proved all-particle Gaussian bound.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology BigOperators

theorem actual_phase_short_square_lower {B : ℂ → ℂ} {φ : ℝ}
    (hB : AnalyticAt ℂ B 0) (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0) :
    ∃ _d : RegularEdgePhaseControl (negativeGlobalCenter B φ) (negativeGlobalCoefficient B),
      ∃ kappa : ℝ, 0 < kappa ∧ ∀ n : ℕ, ∀ q : Fin n → ℝ,
        kappa * angularShortSquare q ≤ (realPhaseTotal B φ n q 0).re := by
  obtain ⟨d, eps, kappa, heps, hk, ha⟩ :=
    exists_negative_global_inward_attenuation hB hφ hπ hBi
  refine ⟨d, kappa, hk, ?_⟩
  intro n q
  have hq (i : Fin n) :
      kappa * unsignedShortAngle (q i) ^ 2 ≤
        (negativeGlobalPhase B φ (0, (q i : ℂ))).re := by
    have hh := (ha 0 le_rfl heps.le).2 (unsignedShortAngle (q i))
      (by rw [abs_of_nonneg (unsignedShortAngle_nonneg _)]; exact unsignedShortAngle_le_pi _)
    simpa only [Complex.ofReal_zero, neg_zero, zero_add, negativeGlobalPhase_unsigned] using hh
  simpa only [angularShortSquare, Finset.mul_sum, realPhaseTotal, Complex.re_sum] using
    Finset.sum_le_sum (s := Finset.univ) (fun i _ => hq i)

theorem exists_actual_outer_phase_control {B : ℂ → ℂ} {φ s : ℝ}
    (hB : AnalyticAt ℂ B 0) (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0)
    (hs : 0 < s) :
    ∃ r eta : ℝ, 0 < r ∧ 0 < eta ∧ eta ≤ 1 ∧ ∀ n : ℕ, 0 < n →
      ∀ q : Fin n → ℝ, s ≤ angularShortSquare q →
      ∀ t ∈ Metric.closedBall (0 : ℂ) (r / (n : ℝ)),
        AnalyticAt ℂ (realPhaseTotal B φ n q) t ∧
        eta / 2 ≤ (realPhaseTotal B φ n q t).re := by
  obtain ⟨d, kappa, hk, hbase⟩ := actual_phase_short_square_lower hB hφ hπ hBi
  let C : ℝ := 2 * d.phaseBound / d.radius
  let eta : ℝ := min (kappa * s) 1
  let r : ℝ := min (d.radius / 2) (eta / (2 * C))
  have hC : 0 < C := div_pos (mul_pos (by norm_num) d.phaseBound_pos) d.radius_pos
  have he : 0 < eta := lt_min (mul_pos hk hs) (by norm_num)
  have hr : 0 < r := lt_min (half_pos d.radius_pos) (by positivity)
  refine ⟨r, eta, hr, he, min_le_right _ _, ?_⟩
  intro n hn q hq t ht
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have htr : t ∈ Metric.closedBall (0 : ℂ) (d.radius / 2) :=
    Metric.closedBall_subset_closedBall ((div_le_self hr.le hn1).trans (min_le_left _ _)) ht
  have hzero : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) (d.radius / 2) :=
    Metric.mem_closedBall_self (half_pos d.radius_pos).le
  have het : eta ≤ (edgeTotalPhase (negativeGlobalCenter B φ) (negativeGlobalCoefficient B) 0 q).re := by
    rw [← realPhaseTotal_eq_edge]
    exact (min_le_left _ _).trans ((mul_le_mul_of_nonneg_left hq hk.le).trans (hbase n q))
  have hdist : (n : ℝ) * (2 * d.phaseBound / d.radius) * ‖t - 0‖ ≤ eta / 2 := by
    rw [sub_zero]
    have hnorm : ‖t‖ ≤ r / (n : ℝ) := by simpa only [Metric.mem_closedBall, dist_zero_right] using ht
    calc
      _ ≤ (n : ℝ) * C * (r / (n : ℝ)) := mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ = C * r := by field_simp
      _ ≤ C * (eta / (2 * C)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le
      _ = eta / 2 := by field_simp
  constructor
  · have heq : realPhaseTotal B φ n q = fun u =>
        edgeTotalPhase (negativeGlobalCenter B φ) (negativeGlobalCoefficient B) u q := by
      funext u
      exact realPhaseTotal_eq_edge B φ n q u
    rw [heq]
    exact d.totalPhase_parameter_analytic q
      (Metric.closedBall_subset_closedBall (half_le_self d.radius_pos.le) htr)
  · simpa only [realPhaseTotal_eq_edge] using d.totalPhase_real_protected q hzero htr het hdist

def realNegativeDensity (b B : ℂ → ℂ) (φ : ℝ) (n : ℕ)
    (t : ℂ) (q : Fin n → ℝ) : ℂ :=
  completeNegativeNumerator n b (negativeGlobalPhase B φ) 0 t (fun i => (q i : ℂ)) *
    phaseSiteFactor (realPhaseTotal B φ n q t)

theorem exists_actual_outer_density_control {b B : ℂ → ℂ} {φ s : ℝ}
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0)
    (hbsq : ∀ t, b t ^ 2 = B t) (hs : 0 < s) :
    ∃ r M kappa : ℝ, 0 < r ∧ 0 < M ∧ 0 < kappa ∧ ∀ n : ℕ, 0 < n →
      ∀ q : Fin n → ℝ, s ≤ angularShortSquare q →
      ∀ t ∈ Metric.closedBall (0 : ℂ) (r / (n : ℝ)),
        AnalyticAt ℂ (fun u => realNegativeDensity b B φ n u q) t ∧
        ‖realNegativeDensity b B φ n t q‖ ≤
          M * Real.exp (-kappa * (n : ℝ) ^ 2) / ‖windingNormalization n‖ := by
  obtain ⟨rp, eta, hrp, he, he1, hp⟩ := exists_actual_outer_phase_control hB hφ hπ hBi hs
  obtain ⟨rh, M, kappa, hrh, hM, hk, hH⟩ :=
    exists_actual_numerator_gaussian_control hb hB hφ hπ hBi hbsq
  let r := min rp rh
  refine ⟨r, M * (8 / eta), kappa, lt_min hrp hrh, by positivity, hk, ?_⟩
  intro n hn q hq t ht
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have htp : t ∈ Metric.closedBall (0 : ℂ) (rp / (n : ℝ)) :=
    Metric.closedBall_subset_closedBall (div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)) ht
  have hth : t ∈ Metric.closedBall (0 : ℂ) rh :=
    Metric.closedBall_subset_closedBall
      ((div_le_self (le_of_lt (lt_min hrp hrh)) hn1).trans (min_le_right _ _)) ht
  obtain ⟨hpa, hpre⟩ := hp n hn q hq t htp
  obtain ⟨hHa, hHb⟩ := hH n q t hth
  constructor
  · exact hHa.mul ((phaseSiteFactor_analyticAt (by linarith :
      0 < (realPhaseTotal B φ n q t).re)).comp hpa)
  · unfold realNegativeDensity
    rw [norm_mul]
    calc
      _ ≤ (M * Real.exp (-kappa * (n : ℝ) ^ 2) / ‖windingNormalization n‖) * (8 / eta) :=
        mul_le_mul hHb (phaseSiteFactor_norm_le he he1 hpre) (norm_nonneg _) (by positivity)
      _ = _ := by ring

end
end IsingBulk.AnisoF002.NegativeHT
