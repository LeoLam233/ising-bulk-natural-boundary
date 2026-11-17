import IsingBulk.AnisoF002.C03.NegativeCoefficientDisks

/-!
# A common genuine complex disk at every strictly inward negative parameter

The N factors in total attenuation and parameter variation cancel.  This
gives local analyticity and termwise differentiation of the complete sum
inside the physical domain, independently of the shrinking boundary disks.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter MeasureTheory IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology BigOperators

namespace NegativeCoefficientControl
variable {B : ℂ → ℂ} {φ : ℝ} (d : NegativeCoefficientControl B φ)

theorem exists_inward_common_disk {eps : ℝ} (he : 0 < eps) (he0 : eps ≤ d.eps0) :
    ∃ r eta : ℝ, 0 < r ∧ 0 < eta ∧ eta ≤ 1 ∧
      ∀ u ∈ Metric.closedBall (-(eps : ℂ)) r,
        u ∈ Metric.closedBall (0 : ℂ) (d.numerator.radius / 2) ∧
        u ∈ Metric.closedBall (0 : ℂ) (d.phase.radius / 2) ∧
        ∀ N : ℕ, 0 < N → ∀ x : Fin N → ℝ,
          eta / 2 ≤ (edgeTotalPhase (negativeGlobalCenter B φ)
            (negativeGlobalCoefficient B) u x).re := by
  let D : ℝ := 2 * d.phase.phaseBound / d.phase.radius
  let eta : ℝ := min 1 (d.attenuation * eps)
  let r : ℝ := min (d.numerator.radius / 4) (min (d.phase.radius / 4) (eta / (2 * D)))
  have hD : 0 < D := div_pos (mul_pos (by norm_num) d.phase.phaseBound_pos) d.phase.radius_pos
  have heta : 0 < eta := lt_min (by norm_num) (mul_pos d.attenuation_pos he)
  have hr : 0 < r := lt_min (div_pos d.numerator.radius_pos (by norm_num))
    (lt_min (div_pos d.phase.radius_pos (by norm_num)) (div_pos heta (mul_pos (by norm_num) hD)))
  have hnum := d.inward_numerator eps he.le he0
  have hphase := d.inward_phase eps he.le he0
  have hsubn : Metric.closedBall (-(eps : ℂ)) r ⊆
      Metric.closedBall (0 : ℂ) (d.numerator.radius / 2) := by
    apply Metric.closedBall_subset_closedBall'
    have ht := Metric.mem_closedBall.mp hnum
    have hrle : r ≤ d.numerator.radius / 4 := min_le_left _ _
    linarith
  have hsubp : Metric.closedBall (-(eps : ℂ)) r ⊆
      Metric.closedBall (0 : ℂ) (d.phase.radius / 2) := by
    apply Metric.closedBall_subset_closedBall'
    have ht := Metric.mem_closedBall.mp hphase
    have hrle : r ≤ d.phase.radius / 4 := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hbase : -(eps : ℂ) ∈ Metric.closedBall (0 : ℂ) (d.phase.radius / 2) :=
    Metric.closedBall_subset_closedBall (by linarith [d.phase.radius_pos]) hphase
  refine ⟨r, eta, hr, heta, min_le_left _ _, ?_⟩
  intro u hu
  refine ⟨hsubn hu, hsubp hu, ?_⟩
  intro N hN x
  have hl (i : Fin N) : eta ≤
      (edgeAnglePhase (negativeGlobalCenter B φ) (negativeGlobalCoefficient B)
        (-(eps : ℂ)) (x i)).re := by
    have hp := d.cosine_lower eps he.le he0 (x i)
    rw [negativeGlobalPhase_real] at hp
    have hx := mul_nonneg d.attenuation_pos.le
      (sub_nonneg.mpr (Real.cos_le_one (x i)))
    have heq : d.attenuation * (eps + 1 - Real.cos (x i)) =
      d.attenuation * eps + d.attenuation * (1 - Real.cos (x i)) := by ring
    rw [heq] at hp
    exact (min_le_right _ _).trans (by linarith)
  have hG : (N : ℝ) * eta ≤
      (edgeTotalPhase (negativeGlobalCenter B φ) (negativeGlobalCoefficient B)
        (-(eps : ℂ)) x).re := by
    simpa only [edgeTotalPhase, Complex.re_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] using
        Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hl i)
  have hdist : (N : ℝ) * D * ‖u - (-(eps : ℂ))‖ ≤ (N : ℝ) * eta / 2 := by
    have hd : ‖u - (-(eps : ℂ))‖ ≤ r := by
      simpa only [dist_eq_norm] using Metric.mem_closedBall.mp hu
    have hrle : r * (2 * D) ≤ eta := (le_div_iff₀ (mul_pos (by norm_num) hD)).mp
      ((min_le_right _ _).trans (min_le_right _ _))
    have hd' : D * ‖u - (-(eps : ℂ))‖ ≤ eta / 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hd hD.le]
    convert mul_le_mul_of_nonneg_left hd' (Nat.cast_nonneg N) using 1 <;> ring
  have hprot := d.phase.totalPhase_real_protected x hbase (hsubp hu) hG hdist
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  exact (by nlinarith : eta / 2 ≤ (N : ℝ) * eta / 2).trans hprot

theorem canonicalCoefficient_analytic_of_phase (n : ℕ) {u : ℂ}
    (hn : u ∈ Metric.closedBall (0 : ℂ) d.numerator.radius)
    (hp : u ∈ Metric.closedBall (0 : ℂ) d.phase.radius)
    (hG : ∀ x : Fin (n + 1) → ℝ,
      0 < (edgeTotalPhase (negativeGlobalCenter B φ) (negativeGlobalCoefficient B) u x).re) :
    AnalyticAt ℂ (negativeCanonicalCoefficient B φ n) u := by
  apply analyticAt_const.mul
  have h := analyticAt_integral_of_joint_analytic
    (μ := regularAngularProbability n)
    (f := edgeJointDensity (negativeGlobalCenter B φ) (negativeGlobalCoefficient B))
    (g := fun q : Fin n → ℝ => complexAngles (negativeConstrainedAngles q))
    (regularAngularBox_compact n) (regularAngularProbability_ae_mem n)
    ((complexAngles_continuous _).comp (negativeConstrainedAngles_continuous n))
    (fun q _ => d.jointDensity_analytic_of_phase (negativeConstrainedAngles q) hn hp (hG _))
  simpa only [edgeJointDensity_real] using h

theorem canonicalCoefficient_norm_of_phase {n : ℕ} {u : ℂ} {E eta : ℝ}
    (heta : 0 < eta) (heta1 : eta ≤ 1) (hE : 0 ≤ E)
    (hG : ∀ x : Fin (n + 1) → ℝ,
      eta / 2 ≤ (edgeTotalPhase (negativeGlobalCenter B φ) (negativeGlobalCoefficient B) u x).re)
    (hnum : ∀ x : Fin (n + 1) → ℝ,
      ‖edgeFullNumerator (negativeGlobalCenter B φ) (negativeGlobalCoefficient B) u x‖ ≤ E) :
    ‖negativeCanonicalCoefficient B φ n u‖ ≤ E * (8 / eta) := by
  unfold negativeCanonicalCoefficient
  rw [norm_mul, norm_inv, norm_natCast]
  apply le_trans (mul_le_mul_of_nonneg_left
    (show ‖∫ q, edgeFullDensity (negativeGlobalCenter B φ) (negativeGlobalCoefficient B)
      u (negativeConstrainedAngles q) ∂regularAngularProbability n‖ ≤ E * (8 / eta) from ?_)
      (inv_nonneg.mpr (Nat.cast_nonneg _)))
    (factorial_inv_mul_le (mul_nonneg hE (by positivity)) _)
  have h := norm_integral_le_of_norm_le_const (μ := regularAngularProbability n) (C := E * (8 / eta))
    (Filter.Eventually.of_forall fun q : Fin n → ℝ => show
      ‖edgeFullDensity (negativeGlobalCenter B φ) (negativeGlobalCoefficient B)
        u (negativeConstrainedAngles q)‖ ≤ E * (8 / eta) from by
          rw [edgeFullDensity, norm_mul]
          exact mul_le_mul (hnum _) (phaseSiteFactor_norm_le heta heta1 (hG _)) (norm_nonneg _) hE)
  simpa [Measure.real] using h

theorem exists_odd_common_disk_majorant {eps : ℝ} (he : 0 < eps) (he0 : eps ≤ d.eps0) :
    ∃ r : ℝ, 0 < r ∧ ∃ M : ℕ → ℝ, Summable M ∧
      (∀ n, AnalyticOnNhd ℂ (negativeCanonicalCoefficient B φ (2 * n))
        (Metric.closedBall (-(eps : ℂ)) r)) ∧
      ∀ n u, u ∈ Metric.closedBall (-(eps : ℂ)) r →
        ‖negativeCanonicalCoefficient B φ (2 * n) u‖ ≤ M n := by
  obtain ⟨r, eta, hr, heta, heta1, hprot⟩ := d.exists_inward_common_disk he he0
  obtain ⟨M0, kappa, hM0, hk, hmatch⟩ := exists_matched_gaussian
    (mul_nonneg d.numerator.prefactorBound_pos.le d.numerator.bodyBound_pos.le)
    d.numerator.pairBound_pos.le d.numerator.rho_pos d.numerator.rho_lt_one
  let M : ℕ → ℝ := fun n => (M0 * (8 / eta)) * Real.exp (-kappa * (2 * (n : ℝ) + 1) ^ 2)
  have hsum : Summable M := by
    apply (Real.summable_exp_nat_mul_of_ge (neg_neg_of_pos hk) ?_).mul_left (M0 * (8 / eta))
    intro n
    have hn := Nat.cast_nonneg (α := ℝ) n
    nlinarith [sq_nonneg (2 * (n : ℝ))]
  refine ⟨r, hr, M, hsum, ?_, ?_⟩
  · intro n u hu
    have hp := hprot u hu
    exact d.canonicalCoefficient_analytic_of_phase _
      (Metric.closedBall_subset_closedBall (half_le_self d.numerator.radius_pos.le) hp.1)
      (Metric.closedBall_subset_closedBall (half_le_self d.phase.radius_pos.le) hp.2.1)
      (fun x => (half_pos heta).trans_le (hp.2.2 _ (by omega) x))
  · intro n u hu
    have hp := hprot u hu
    have hnum (x : Fin (2 * n + 1) → ℝ) :
        ‖edgeFullNumerator (negativeGlobalCenter B φ) (negativeGlobalCoefficient B) u x‖ ≤
          M0 * Real.exp (-kappa * (2 * (n : ℝ) + 1) ^ 2) := by
      simpa only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, one_mul, pow_zero,
        div_one, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
          d.numerator.fullNumerator_gaussian hmatch x hp.1 0
    have hh := canonicalCoefficient_norm_of_phase heta heta1
      (mul_nonneg hM0.le (Real.exp_pos _).le) (hp.2.2 _ (by omega)) hnum
    convert hh using 1
    dsimp [M]
    ring

end NegativeCoefficientControl
end
end IsingBulk.AnisoF002.NegativeHT
