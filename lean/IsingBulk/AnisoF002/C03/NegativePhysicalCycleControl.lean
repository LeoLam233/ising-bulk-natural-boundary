import IsingBulk.AnisoF002.C03.NegativeOuterCycleControl
import IsingBulk.AnisoF002.C03.NegativeCoefficientDisks
import IsingBulk.AnisoF002.C03.NegativeInnerMeasurableRemainder

/-!
# Actual density control on every complete odd real cycle

The original zero-sum momentum constraint gives a strictly positive phase
on a c/N² disk.  This both controls the original density and proves that
the same extracted moving pole lies outside that disk.  No distance from
an arbitrarily chosen residue contour is assumed.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology

theorem exists_actual_physical_cycle_control {b B : ℂ → ℂ} {φ : ℝ}
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0)
    (hbsq : ∀ t, b t ^ 2 = B t) :
    ∃ c M kappa A : ℝ, 0 < c ∧ 0 < M ∧ 0 < kappa ∧ 0 < A ∧
      ∀ n : ℕ, Odd (n + 1) → ∀ q : Fin n → ℝ,
      ∀ t ∈ Metric.closedBall (0 : ℂ) (c / ((n + 1 : ℕ) : ℝ) ^ 2),
        AnalyticAt ℂ (fun u => realNegativeDensity b B φ (n + 1) u (negativeConstrainedAngles q)) t ∧
        A / (n + 1 : ℕ) ≤ (realPhaseTotal B φ (n + 1) (negativeConstrainedAngles q) t).re ∧
        ‖realNegativeDensity b B φ (n + 1) t (negativeConstrainedAngles q)‖ ≤
          M * ((n + 1 : ℕ) : ℝ) * Real.exp (-kappa * ((n + 1 : ℕ) : ℝ) ^ 2) /
            ‖windingNormalization (n + 1)‖ := by
  obtain ⟨d⟩ := exists_negative_coefficient_control hB hφ hπ hBi
  obtain ⟨rh, M, kappa, hrh, hM, hk, hnum⟩ :=
    exists_actual_numerator_gaussian_control hb hB hφ hπ hBi hbsq
  let c := min d.coefficientConstant rh
  let A := d.phaseConstant / 2
  have hc : 0 < c := lt_min d.coefficientConstant_pos hrh
  refine ⟨c, M * (8 / d.phaseConstant), kappa, A, hc,
    mul_pos hM (div_pos (by norm_num) d.phaseConstant_pos), hk,
    half_pos d.phaseConstant_pos, ?_⟩
  intro n hn q t ht
  have hN : 0 < (n + 1 : ℕ) := Nat.succ_pos n
  have hNR : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hN1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hNd : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
  have htc : t ∈ Metric.closedBall (-(0 : ℂ)) (d.coefficientRadius (n + 1)) := by
    rw [neg_zero]
    exact Metric.closedBall_subset_closedBall
      (div_le_div_of_nonneg_right (min_le_left _ _) (sq_nonneg _)) ht
  have hth : t ∈ Metric.closedBall (0 : ℂ) rh := Metric.closedBall_subset_closedBall
    ((div_le_self hc.le hNd).trans (min_le_right _ _)) ht
  have hp := d.coefficientDisk_phase_protected hn le_rfl d.eps0_pos.le
    (flatConstrainedAngles q) (flatConstrainedAngles_sum n q) htc
  have hp' : (d.phaseConstant / ((n + 1 : ℕ) : ℝ)) / 2 ≤
      (realPhaseTotal B φ (n + 1) (negativeConstrainedAngles q) t).re := by
    rw [realPhaseTotal_eq_edge]
    change (d.phaseConstant / ((n + 1 : ℕ) : ℝ)) / 2 ≤
      (edgeTotalPhase (negativeGlobalCenter B φ) (negativeGlobalCoefficient B) t
        (fun i => flatConstrainedAngles q i - Real.pi)).re
    exact hp.2
  have hpos : 0 < (realPhaseTotal B φ (n + 1) (negativeConstrainedAngles q) t).re :=
    (half_pos (div_pos d.phaseConstant_pos hNR)).trans_le hp'
  have hphase : AnalyticAt ℂ (realPhaseTotal B φ (n + 1) (negativeConstrainedAngles q)) t := by
    have heq : realPhaseTotal B φ (n + 1) (negativeConstrainedAngles q) = fun u =>
        edgeTotalPhase (negativeGlobalCenter B φ) (negativeGlobalCoefficient B) u (negativeConstrainedAngles q) := by
      funext u
      exact realPhaseTotal_eq_edge B φ (n + 1) _ u
    rw [heq]
    exact d.phase.totalPhase_parameter_analytic _ (Metric.closedBall_subset_closedBall
      (half_le_self d.phase.radius_pos.le) hp.1)
  obtain ⟨hHa, hHb⟩ := hnum (n + 1) (negativeConstrainedAngles q) t hth
  refine ⟨hHa.mul ((phaseSiteFactor_analyticAt hpos).comp hphase), ?_, ?_⟩
  · convert hp' using 1
    dsimp [A]
    ring
  · unfold realNegativeDensity
    rw [norm_mul]
    have he := d.phase_eta_bounds hN
    have hsite := phaseSiteFactor_norm_le he.1 he.2 hp'
    calc
      _ ≤ (M * Real.exp (-kappa * ((n + 1 : ℕ) : ℝ) ^ 2) / ‖windingNormalization (n + 1)‖) *
          (8 / (d.phaseConstant / ((n + 1 : ℕ) : ℝ))) :=
        mul_le_mul hHb hsite (norm_nonneg _) (by positivity)
      _ = _ := by field_simp

theorem extracted_pole_outside_physical_disk {b B : ℂ → ℂ} {φ r s M kappa c A : ℝ} {n : ℕ}
    (d : InnerRemainderFamily b B φ (n + 1) r s M kappa)
    (_hc : 0 < c) (hA : 0 < A) (q : Fin n → ℝ)
    (hq : angularShortSquare (negativeConstrainedAngles q) ≤ s)
    (hphase : ∀ t ∈ Metric.closedBall (0 : ℂ) (c / ((n + 1 : ℕ) : ℝ) ^ 2),
      A / (n + 1 : ℕ) ≤ (realPhaseTotal B φ (n + 1) (negativeConstrainedAngles q) t).re) :
    c / ((n + 1 : ℕ) : ℝ) ^ 2 < ‖d.pole (negativeConstrainedAngles q)‖ := by
  have hN : 0 < (n + 1 : ℕ) := Nat.succ_pos n
  have hNR : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  by_contra hnot
  have ht : d.pole (negativeConstrainedAngles q) ∈
      Metric.closedBall (0 : ℂ) (c / ((n + 1 : ℕ) : ℝ) ^ 2) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using le_of_not_gt hnot
  have heq := realPhaseTotal_eq_average B φ hN (negativeConstrainedAngles q) (d.pole (negativeConstrainedAngles q))
  rw [d.pole_zero ⟨negativeConstrainedAngles q, hq⟩, mul_zero, add_zero] at heq
  have hh := hphase _ ht
  rw [heq] at hh
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.natCast_im, mul_zero, zero_mul, sub_self] at hh
  exact (not_le_of_gt (div_pos hA hNR)) hh

end
end IsingBulk.AnisoF002.NegativeHT
