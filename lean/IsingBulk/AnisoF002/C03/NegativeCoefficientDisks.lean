import IsingBulk.AnisoF002.C03.NegativeCoefficientControl

/-!
# Complete negative-edge angular coefficients on their actual analytic disks

The n index counts independent angles, so the particle population is n+1.
The final momentum is minus their sum and all angles are then shifted by
pi.  Every numerator factor and the full rational site factor is retained.
The separate physical-root identity supplies the constant unit phase.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter MeasureTheory IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology BigOperators

def negativeConstrainedAngles {n : ℕ} (q : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  fun i => flatConstrainedAngles q i - Real.pi

theorem flatConstrainedAngles_sum (n : ℕ) (q : Fin n → ℝ) :
    ∑ i, flatConstrainedAngles q i = 0 := by
  simp [flatConstrainedAngles, Fin.sum_univ_castSucc]

theorem negativeConstrainedAngles_continuous (n : ℕ) :
    Continuous (negativeConstrainedAngles (n := n)) :=
  continuous_pi fun i => ((continuous_apply i).comp (flatConstrainedAngles_continuous n)).sub
    continuous_const

def negativeCanonicalCoefficient (B : ℂ → ℂ) (φ : ℝ) (n : ℕ) (t : ℂ) : ℂ :=
  ((n + 1).factorial : ℂ)⁻¹ *
    ∫ q, edgeFullDensity (negativeGlobalCenter B φ) (negativeGlobalCoefficient B)
      t (negativeConstrainedAngles q) ∂regularAngularProbability n

theorem negativeCanonicalCoefficient_normalization (B : ℂ → ℂ) (φ : ℝ) (n : ℕ) (t : ℂ) :
    negativeCanonicalCoefficient B φ n t = (windingNormalization (n + 1))⁻¹ *
      ∫ q in regularAngularBox n,
        edgeFullDensity (negativeGlobalCenter B φ) (negativeGlobalCoefficient B)
          t (negativeConstrainedAngles q) := by
  rw [negativeCanonicalCoefficient, regularAngularProbability_integral]
  simp only [Complex.real_smul, one_div, Complex.ofReal_inv, Complex.ofReal_pow,
    Complex.ofReal_mul, Complex.ofReal_ofNat, windingNormalization, Nat.add_sub_cancel,
    mul_inv_rev]
  ring

namespace NegativeCoefficientControl
variable {B : ℂ → ℂ} {φ : ℝ} (d : NegativeCoefficientControl B φ)

theorem jointDensity_analytic_of_phase {N : ℕ} (x : Fin N → ℝ) {u : ℂ}
    (hn : u ∈ Metric.closedBall (0 : ℂ) d.numerator.radius)
    (hp : u ∈ Metric.closedBall (0 : ℂ) d.phase.radius)
    (hG : 0 < (edgeTotalPhase (negativeGlobalCenter B φ) (negativeGlobalCoefficient B) u x).re) :
    AnalyticAt ℂ (edgeJointDensity (negativeGlobalCenter B φ) (negativeGlobalCoefficient B))
      (u, complexAngles x) := by
  have hcos (i : Fin N) : Complex.cos (complexAngles x i) = (Real.cos (x i) : ℂ) := by
    simp [complexAngles, Complex.ofReal_cos]
  apply (d.numerator.jointNumerator_analytic hn ?_).mul
    ((phaseSiteFactor_analyticAt ?_).comp (d.phase.jointTotalPhase_analytic hp ?_))
  · intro i
    rw [hcos]
    exact Metric.self_subset_thickening d.numerator.cosineRadius_pos _
      (real_cos_mem_complexCosineInterval (x i))
  · rwa [edgeJointTotalPhase_real]
  · intro i
    rw [hcos]
    exact Metric.self_subset_thickening d.phase.cosineRadius_pos _
      (real_cos_mem_complexCosineInterval (x i))

theorem coefficient_analytic_on_disk {n : ℕ} (hn : Odd (n + 1)) {eps : ℝ}
    (he : 0 ≤ eps) (he0 : eps ≤ d.eps0) :
    AnalyticOnNhd ℂ (negativeCanonicalCoefficient B φ n)
      (Metric.closedBall (-(eps : ℂ)) (d.coefficientRadius (n + 1))) := by
  intro u hu
  apply analyticAt_const.mul
  have h := analyticAt_integral_of_joint_analytic
    (μ := regularAngularProbability n)
    (f := edgeJointDensity (negativeGlobalCenter B φ) (negativeGlobalCoefficient B))
    (g := fun q : Fin n → ℝ => complexAngles (negativeConstrainedAngles q))
    (regularAngularBox_compact n) (regularAngularProbability_ae_mem n)
    ((complexAngles_continuous _).comp (negativeConstrainedAngles_continuous n))
    (fun q _ => show AnalyticAt ℂ
      (edgeJointDensity (negativeGlobalCenter B φ) (negativeGlobalCoefficient B))
      (u, complexAngles (negativeConstrainedAngles q)) from by
        have hp := d.coefficientDisk_phase_protected hn he he0 (flatConstrainedAngles q)
          (flatConstrainedAngles_sum n q) hu
        exact d.jointDensity_analytic_of_phase _
          (Metric.closedBall_subset_closedBall (half_le_self d.numerator.radius_pos.le)
            (d.coefficientDisk_numerator_subset hn.pos he he0 hu))
          (Metric.closedBall_subset_closedBall (half_le_self d.phase.radius_pos.le) hp.1)
          ((half_pos (d.phase_eta_bounds hn.pos).1).trans_le hp.2))
  simpa only [edgeJointDensity_real] using h

theorem coefficient_norm_on_disk {n : ℕ} (hn : Odd (n + 1)) {eps E : ℝ}
    (he : 0 ≤ eps) (he0 : eps ≤ d.eps0) {u : ℂ}
    (hu : u ∈ Metric.closedBall (-(eps : ℂ)) (d.coefficientRadius (n + 1)))
    (hE : 0 ≤ E)
    (hnum : ∀ x : Fin (n + 1) → ℝ,
      ‖edgeFullNumerator (negativeGlobalCenter B φ) (negativeGlobalCoefficient B) u x‖ ≤ E) :
    ‖negativeCanonicalCoefficient B φ n u‖ ≤ E * (8 * (n + 1 : ℕ) / d.phaseConstant) := by
  let eta := d.phaseConstant / (n + 1 : ℕ)
  have heta : 0 < eta ∧ eta ≤ 1 := d.phase_eta_bounds hn.pos
  unfold negativeCanonicalCoefficient
  rw [norm_mul, norm_inv, norm_natCast]
  have hI : ‖∫ q, edgeFullDensity (negativeGlobalCenter B φ) (negativeGlobalCoefficient B)
      u (negativeConstrainedAngles q) ∂regularAngularProbability n‖ ≤ E * (8 / eta) := by
    have h := norm_integral_le_of_norm_le_const
      (μ := regularAngularProbability n) (C := E * (8 / eta))
      (Filter.Eventually.of_forall fun q : Fin n → ℝ => show
        ‖edgeFullDensity (negativeGlobalCenter B φ) (negativeGlobalCoefficient B)
          u (negativeConstrainedAngles q)‖ ≤ E * (8 / eta) from by
            rw [edgeFullDensity, norm_mul]
            exact mul_le_mul (hnum _) (phaseSiteFactor_norm_le heta.1 heta.2
              (d.coefficientDisk_phase_protected hn he he0 (flatConstrainedAngles q)
                (flatConstrainedAngles_sum n q) hu).2) (norm_nonneg _) hE)
    simpa [Measure.real] using h
  have hb := (mul_le_mul_of_nonneg_left hI
    (inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) (n + 1).factorial))).trans
    (factorial_inv_mul_le (mul_nonneg hE (div_nonneg (by norm_num) heta.1.le)) (n + 1))
  convert hb using 1
  dsimp [eta]
  field_simp

theorem exists_coefficient_gaussian_disks :
    ∃ M kappa : ℝ, 0 < M ∧ 0 < kappa ∧
      ∀ n : ℕ, Odd (n + 1) → ∀ eps : ℝ, 0 ≤ eps → eps ≤ d.eps0 →
        ∀ u ∈ Metric.closedBall (-(eps : ℂ)) (d.coefficientRadius (n + 1)),
          ‖negativeCanonicalCoefficient B φ n u‖ ≤
            M * (n + 1 : ℕ) * Real.exp (-kappa * ((n + 1 : ℕ) : ℝ) ^ 2) := by
  obtain ⟨M0, kappa, hM0, hk, hmatch⟩ := exists_matched_gaussian
    (mul_nonneg d.numerator.prefactorBound_pos.le d.numerator.bodyBound_pos.le)
    d.numerator.pairBound_pos.le d.numerator.rho_pos d.numerator.rho_lt_one
  refine ⟨M0 * 8 / d.phaseConstant, kappa,
    div_pos (mul_pos hM0 (by norm_num)) d.phaseConstant_pos, hk, ?_⟩
  intro n hn eps he he0 u hu
  have hnum (x : Fin (n + 1) → ℝ) :
      ‖edgeFullNumerator (negativeGlobalCenter B φ) (negativeGlobalCoefficient B) u x‖ ≤
        M0 * Real.exp (-kappa * ((n + 1 : ℕ) : ℝ) ^ 2) := by
    simpa only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, one_mul, pow_zero,
      div_one] using d.numerator.fullNumerator_gaussian hmatch x
        (d.coefficientDisk_numerator_subset hn.pos he he0 hu) 0
  have hh := d.coefficient_norm_on_disk hn he he0 hu
    (mul_nonneg hM0.le (Real.exp_pos _).le) hnum
  convert hh using 1
  ring

end NegativeCoefficientControl
end
end IsingBulk.AnisoF002.NegativeHT
