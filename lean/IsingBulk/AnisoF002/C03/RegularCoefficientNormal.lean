import IsingBulk.AnisoF002.C03.RegularAngularSplit
import IsingBulk.AnisoF002.C03.RegularCompactAnalytic
import IsingBulk.AnisoF002.C03.RegularEdgeGaussian

/-!
# A common complex disk for every actual regular-edge coefficient

At any positive inward distance, the total attenuation and the phase
variation both grow linearly with N.  Their N factors cancel, giving a
single genuine complex disk on which every rational pole is protected.
The complete coefficient series then has a summable Gaussian majorant.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators

theorem flatConstrainedAngles_continuous (n : ℕ) :
    Continuous (flatConstrainedAngles (n := n)) :=
  continuous_id.finSnoc (A := fun _ : Fin (n + 1) => ℝ)
    (continuous_finsetSum _ fun i _ => continuous_apply i).neg

namespace RegularEdgeCompleteControl
variable {b : ℝ} {a : ℂ → ℂ} (d : RegularEdgeCompleteControl b a)

theorem jointDensity_analytic_of_phase {N : ℕ} (x : Fin N → ℝ) {u : ℂ}
    (hu : u ∈ Metric.closedBall (0 : ℂ) d.phase.radius)
    (hG : 0 < (edgeTotalPhase (affineEdgeCenter b) a u x).re) :
    AnalyticAt ℂ (edgeJointDensity (affineEdgeCenter b) a) (u, complexAngles x) := by
  have hn := Metric.closedBall_subset_closedBall d.radius_le hu
  have hcos (i : Fin N) : Complex.cos (complexAngles x i) = (Real.cos (x i) : ℂ) := by
    simp [complexAngles, Complex.ofReal_cos]
  apply (d.numerator.jointNumerator_analytic hn ?_).mul
    ((phaseSiteFactor_analyticAt ?_).comp (d.phase.jointTotalPhase_analytic hu ?_))
  · intro i
    rw [hcos]
    exact Metric.self_subset_thickening d.numerator.cosineRadius_pos _
      (real_cos_mem_complexCosineInterval (x i))
  · rwa [edgeJointTotalPhase_real]
  · intro i
    rw [hcos]
    exact Metric.self_subset_thickening d.phase.cosineRadius_pos _
      (real_cos_mem_complexCosineInterval (x i))

theorem particleCoefficient_analytic_of_phase (n : ℕ) {u : ℂ}
    (hu : u ∈ Metric.closedBall (0 : ℂ) d.phase.radius)
    (hG : ∀ x : Fin (n + 1) → ℝ, 0 < (edgeTotalPhase (affineEdgeCenter b) a u x).re) :
    AnalyticAt ℂ (edgeParticleCoefficient (affineEdgeCenter b) a n) u := by
  apply analyticAt_const.mul
  have h := analyticAt_integral_of_joint_analytic
    (μ := regularAngularProbability n) (f := edgeJointDensity (affineEdgeCenter b) a)
    (g := fun q : Fin n → ℝ => complexAngles (flatConstrainedAngles q))
    (regularAngularBox_compact n) (regularAngularProbability_ae_mem n)
    ((complexAngles_continuous _).comp (flatConstrainedAngles_continuous n))
    (fun q _ => d.jointDensity_analytic_of_phase (flatConstrainedAngles q) hu (hG _))
  simpa only [edgeJointDensity_real] using h

theorem inward_anglePhase_uniform_lower {eps : ℝ}
    (he : 0 < eps) (he0 : eps ≤ d.eps0) (q : ℝ) :
    eps / Real.exp d.phase.phaseBound ≤
      (edgeAnglePhase (affineEdgeCenter b) a ((eps : ℂ) * Complex.I) q).re := by
  let W := affineEdgeCenter b ((eps : ℂ) * Complex.I) +
    a ((eps : ℂ) * Complex.I) * (1 - (Real.cos q : ℂ))
  have hw : eps ≤ W.im := by
    rw [show W.im = eps + (a ((eps : ℂ) * Complex.I)).im * (1 - Real.cos q) from
      inward_dispersion_im b a eps q]
    exact le_add_of_nonneg_right (mul_nonneg (d.coefficient_im_pos eps he he0).le
      (sub_nonneg.mpr (Real.cos_le_one q)))
  have ht : (eps : ℂ) * Complex.I ∈ Metric.closedBall (0 : ℂ) d.phase.radius :=
    Metric.closedBall_subset_closedBall (by linarith [d.phase.radius_pos]) (d.inward_mem eps he he0)
  exact (div_le_div_of_nonneg_right hw (Real.exp_pos _).le).trans
    (upperEdgePhase_re_ge_im_div_exp (he.trans_le hw) (d.phase.phase_bound _ ht q))

/-- The radius is independent of both particle number and real angles. -/
theorem exists_inward_common_pole_disk {eps : ℝ} (he : 0 < eps) (he0 : eps ≤ d.eps0) :
    ∃ r eta : ℝ, 0 < r ∧ 0 < eta ∧ eta ≤ 1 ∧
      ∀ u ∈ Metric.closedBall ((eps : ℂ) * Complex.I) r,
        u ∈ Metric.closedBall (0 : ℂ) (d.phase.radius / 2) ∧
        ∀ N : ℕ, 0 < N → ∀ x : Fin N → ℝ,
          eta / 2 ≤ (edgeTotalPhase (affineEdgeCenter b) a u x).re := by
  let D := 2 * d.phase.phaseBound / d.phase.radius
  let eta := min 1 (eps / Real.exp d.phase.phaseBound)
  let r := min (d.phase.radius / 4) (eta / (2 * D))
  have hD : 0 < D := div_pos (mul_pos (by norm_num) d.phase.phaseBound_pos) d.phase.radius_pos
  have heta : 0 < eta := lt_min (by norm_num) (div_pos he (Real.exp_pos _))
  have hr : 0 < r := lt_min (div_pos d.phase.radius_pos (by norm_num))
    (div_pos heta (mul_pos (by norm_num) hD))
  have ht := d.inward_mem eps he he0
  have hsub : Metric.closedBall ((eps : ℂ) * Complex.I) r ⊆
      Metric.closedBall (0 : ℂ) (d.phase.radius / 2) := by
    apply Metric.closedBall_subset_closedBall'
    have hd := Metric.mem_closedBall.mp ht
    have hrle : r ≤ d.phase.radius / 4 := min_le_left _ _
    linarith
  have ht' : (eps : ℂ) * Complex.I ∈ Metric.closedBall (0 : ℂ) (d.phase.radius / 2) :=
    Metric.closedBall_subset_closedBall (by linarith [d.phase.radius_pos]) ht
  refine ⟨r, eta, hr, heta, min_le_left _ _, ?_⟩
  intro u hu
  refine ⟨hsub hu, ?_⟩
  intro N hN x
  have hG : (N : ℝ) * eta ≤
      (edgeTotalPhase (affineEdgeCenter b) a ((eps : ℂ) * Complex.I) x).re := by
    have hl (i : Fin N) : eta ≤
        (edgeAnglePhase (affineEdgeCenter b) a ((eps : ℂ) * Complex.I) (x i)).re :=
      (min_le_right _ _).trans (d.inward_anglePhase_uniform_lower he he0 (x i))
    simpa only [edgeTotalPhase, Complex.re_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hl i)
  have hdist : (N : ℝ) * D * ‖u - (eps : ℂ) * Complex.I‖ ≤ (N : ℝ) * eta / 2 := by
    have hd : ‖u - (eps : ℂ) * Complex.I‖ ≤ r := by
      simpa only [dist_eq_norm] using Metric.mem_closedBall.mp hu
    have hrle : r * (2 * D) ≤ eta :=
      (le_div_iff₀ (mul_pos (by norm_num) hD)).mp (min_le_right _ _)
    have hd' : D * ‖u - (eps : ℂ) * Complex.I‖ ≤ eta / 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hd hD.le]
    convert mul_le_mul_of_nonneg_left hd' (Nat.cast_nonneg N) using 1 <;> ring
  have hphase := d.phase.totalPhase_real_protected x ht' (hsub hu) hG hdist
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  exact (by nlinarith : eta / 2 ≤ (N : ℝ) * eta / 2).trans hphase

theorem particleCoefficient_norm_le {n : ℕ} {u : ℂ} {E eta : ℝ}
    (heta : 0 < eta) (heta1 : eta ≤ 1) (hE : 0 ≤ E)
    (hG : ∀ x : Fin (n + 1) → ℝ, eta / 2 ≤ (edgeTotalPhase (affineEdgeCenter b) a u x).re)
    (hnum : ∀ x : Fin (n + 1) → ℝ, ‖edgeFullNumerator (affineEdgeCenter b) a u x‖ ≤ E) :
    ‖edgeParticleCoefficient (affineEdgeCenter b) a n u‖ ≤ E * (8 / eta) := by
  unfold edgeParticleCoefficient
  rw [norm_mul, norm_inv, norm_natCast]
  apply le_trans (mul_le_mul_of_nonneg_left
    (show ‖∫ q, edgeFullDensity (affineEdgeCenter b) a u (flatConstrainedAngles q)
      ∂regularAngularProbability n‖ ≤ E * (8 / eta) from ?_) (inv_nonneg.mpr (Nat.cast_nonneg _)))
    (factorial_inv_mul_le (mul_nonneg hE (by positivity)) _)
  have h := norm_integral_le_of_norm_le_const
    (μ := regularAngularProbability n) (C := E * (8 / eta))
    (Filter.Eventually.of_forall fun q : Fin n → ℝ => show
      ‖edgeFullDensity (affineEdgeCenter b) a u (flatConstrainedAngles q)‖ ≤ E * (8 / eta) from by
        rw [edgeFullDensity, norm_mul]
        exact mul_le_mul (hnum _) (phaseSiteFactor_norm_le heta heta1 (hG _)) (norm_nonneg _) hE)
  simpa [Measure.real] using h

/-- The single flat coefficient family has a summable common-disk
majorant for every fixed starting index and both parity subsequences. -/
theorem exists_particle_subseries_common_disk (m : ℕ) {eps : ℝ}
    (he : 0 < eps) (he0 : eps ≤ d.eps0) :
    ∃ r : ℝ, 0 < r ∧ ∃ M : ℕ → ℝ, Summable M ∧
      (∀ n, AnalyticOnNhd ℂ (edgeParticleCoefficient (affineEdgeCenter b) a (m + 2 * n))
        (Metric.closedBall ((eps : ℂ) * Complex.I) r)) ∧
      ∀ n u, u ∈ Metric.closedBall ((eps : ℂ) * Complex.I) r →
        ‖edgeParticleCoefficient (affineEdgeCenter b) a (m + 2 * n) u‖ ≤ M n := by
  obtain ⟨r, eta, hr, heta, heta1, hprot⟩ := d.exists_inward_common_pole_disk he he0
  obtain ⟨M0, kappa, hM0, hk, hmatch⟩ := exists_matched_gaussian
    (mul_nonneg d.numerator.prefactorBound_pos.le d.numerator.bodyBound_pos.le)
    d.numerator.pairBound_pos.le d.numerator.rho_pos d.numerator.rho_lt_one
  let M : ℕ → ℝ := fun n => (M0 * (8 / eta)) * Real.exp (-kappa * ((m : ℝ) + 2 * n + 1) ^ 2)
  have hsum : Summable M := by
    apply (Real.summable_exp_nat_mul_of_ge (neg_neg_of_pos hk) ?_).mul_left (M0 * (8 / eta))
    intro n
    have hn := Nat.cast_nonneg (α := ℝ) n
    have hm := Nat.cast_nonneg (α := ℝ) m
    nlinarith [sq_nonneg ((m : ℝ) + 2 * n)]
  refine ⟨r, hr, M, hsum, ?_, ?_⟩
  · intro n u hu
    have hp := hprot u hu
    exact d.particleCoefficient_analytic_of_phase _
      (Metric.closedBall_subset_closedBall (half_le_self d.phase.radius_pos.le) hp.1)
      (fun x => (half_pos heta).trans_le (hp.2 _ (by omega) x))
  · intro n u hu
    have hp := hprot u hu
    have hn : u ∈ Metric.closedBall (0 : ℂ) (d.numerator.radius / 2) :=
      Metric.closedBall_subset_closedBall (by linarith [d.radius_le]) hp.1
    have hnum (x : Fin (m + 2 * n + 1) → ℝ) :
        ‖edgeFullNumerator (affineEdgeCenter b) a u x‖ ≤
          M0 * Real.exp (-kappa * ((m : ℝ) + 2 * n + 1) ^ 2) := by
      simpa only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, one_mul, pow_zero,
        div_one, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
        d.numerator.fullNumerator_gaussian hmatch x hn 0
    have hh := particleCoefficient_norm_le heta heta1 (mul_nonneg hM0.le (Real.exp_pos _).le)
      (hp.2 _ (by omega)) hnum
    convert hh using 1
    dsimp [M]
    ring

end RegularEdgeCompleteControl
end
end IsingBulk.AnisoF002.RegularTail.C03
