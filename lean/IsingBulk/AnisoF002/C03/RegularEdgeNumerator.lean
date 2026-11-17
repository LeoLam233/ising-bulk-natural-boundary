import IsingBulk.AnisoF002.C03.RegularEdgeControl
import IsingBulk.AnisoF002.C03.RegularMatchedSummation

/-!
# Complete regular-edge numerator estimates from the constructed chart

The matching hypotheses are now discharged for the explicit continued
root.  The full numerator contains every pair, every one-body factor and
the analytic square-root anisotropy prefactor.  All fixed parameter jets
are bounded uniformly on one smaller disk and for every real angular tuple.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open IsingBulk.AnisoF002.Isotropic
open scoped BigOperators Topology

def edgeFullNumerator {N : ℕ} (c a : ℂ → ℂ) (t : ℂ) (x : Fin N → ℝ) : ℂ :=
  branchFullNumerator (a t) (edgePrefactor a t) (edgeAngleRoot c a t) x

theorem edgeAngleRoot_dispersion (c a : ℂ → ℂ) (t : ℂ) (q : ℝ) :
    (1 : ℂ) * edgeAngleRoot c a t q ^ 2 -
      2 * ((c t + a t) - a t * (Real.cos q : ℂ)) * edgeAngleRoot c a t q + 1 = 0 := by
  have hp := upperEdgeRoot_polynomial (c t + a t * (1 - (Real.cos q : ℂ)))
  change edgeAngleRoot c a t q ^ 2 -
    2 * (c t + a t * (1 - (Real.cos q : ℂ))) * edgeAngleRoot c a t q + 1 = 0 at hp
  linear_combination hp

namespace RegularEdgeControl
variable {c a : ℂ → ℂ} (d : RegularEdgeControl c a)

theorem real_pair_protected {t : ℂ} (ht : t ∈ Metric.closedBall (0 : ℂ) d.radius)
    (q s : ℝ) :
    (t, (Real.cos q : ℂ), (Real.cos s : ℂ)) ∈ protectedPairSet (edgeJointRoot c a) d.rho :=
  d.protected_pairs t ht _ (Metric.self_subset_thickening d.cosineRadius_pos _
    (real_cos_mem_complexCosineInterval q)) _ (Metric.self_subset_thickening d.cosineRadius_pos _
      (real_cos_mem_complexCosineInterval s))

theorem root_denominator {t : ℂ} (ht : t ∈ Metric.closedBall (0 : ℂ) d.radius)
    (q s : ℝ) : 1 - edgeAngleRoot c a t q * edgeAngleRoot c a t s ≠ 0 :=
  (d.real_pair_protected ht q s).2.2.1

theorem root_schur_bound {t : ℂ} (ht : t ∈ Metric.closedBall (0 : ℂ) d.radius)
    (q s : ℝ) : ‖schur (edgeAngleRoot c a t q) (edgeAngleRoot c a t s)‖ ≤ d.rho :=
  (d.real_pair_protected ht q s).2.2.2.le

theorem angleRoot_continuous {t : ℂ} (ht : t ∈ Metric.closedBall (0 : ℂ) d.radius) :
    Continuous (edgeAngleRoot c a t) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  have hm : ContinuousAt (fun s : ℝ => (t, (Real.cos s : ℂ))) q := by fun_prop
  exact ContinuousAt.comp (g := edgeJointRoot c a)
    (d.real_pair_protected ht q q).1.continuousAt hm

theorem angleRoot_parameter_analytic {t : ℂ}
    (ht : t ∈ Metric.closedBall (0 : ℂ) d.radius) (q : ℝ) :
    AnalyticAt ℂ (fun u => edgeAngleRoot c a u q) t :=
  (d.real_pair_protected ht q q).1.comp
    (f := fun u : ℂ => (u, (Real.cos q : ℂ))) (analyticAt_id.prod analyticAt_const)

theorem body_parameter_analytic {t : ℂ}
    (ht : t ∈ Metric.closedBall (0 : ℂ) d.radius) (q : ℝ) :
    AnalyticAt ℂ (fun u => branchOneBody (edgeAngleRoot c a u) q) t := by
  have h := d.real_pair_protected ht q q
  exact (edgeOneBody_analyticAt h.1 h.2.2.1).comp
    (f := fun u : ℂ => (u, (Real.cos q : ℂ))) (analyticAt_id.prod analyticAt_const)

theorem pair_parameter_analytic {t : ℂ}
    (ht : t ∈ Metric.closedBall (0 : ℂ) d.radius) (q s : ℝ) :
    AnalyticAt ℂ (fun u => branchCanceledPair (a u) (edgeAngleRoot c a u) q s) t := by
  have h := edgeSineCoefficient_analyticAt (d.coefficient_analytic t ht)
    (d.real_pair_protected ht q s)
  have hc : AnalyticAt ℂ (fun u => sinePairCoefficient (a u)
      (edgeAngleRoot c a u q) (edgeAngleRoot c a u s)) t :=
    h.comp (f := fun u : ℂ => (u, (Real.cos q : ℂ), (Real.cos s : ℂ)))
      (analyticAt_id.prod analyticAt_const)
  have he : (fun u => branchCanceledPair (a u) (edgeAngleRoot c a u) q s) =
      fun u => sinePairCoefficient (a u) (edgeAngleRoot c a u q) (edgeAngleRoot c a u s) *
        (Real.sin ((q - s) / 2) ^ 2 : ℝ) := by
    funext u
    exact branchCanceledPair_eq_real_sine _ _ _ _
  rw [he]
  exact hc.mul analyticAt_const

theorem fullNumerator_analytic {N : ℕ} (x : Fin N → ℝ) {t : ℂ}
    (ht : t ∈ Metric.closedBall (0 : ℂ) d.radius) :
    AnalyticAt ℂ (fun u => edgeFullNumerator c a u x) t := by
  unfold edgeFullNumerator branchFullNumerator
  exact (((d.prefactor_analytic t ht).pow N).mul
    (Finset.univ.analyticAt_fun_prod fun i _ => d.body_parameter_analytic ht (x i))).mul
    ((indexPairs N).analyticAt_fun_prod fun ij _ => d.pair_parameter_analytic ht (x ij.1) (x ij.2))

theorem pairs_even_bound {t : ℂ} (ht : t ∈ Metric.closedBall (0 : ℂ) d.radius)
    (n : ℕ) (x : Fin (2 * n) → ℝ) :
    ‖∏ ij ∈ indexPairs (2 * n), branchCanceledPair (a t) (edgeAngleRoot c a t) (x ij.1) (x ij.2)‖ ≤
      (matchingNumber n : ℝ) * d.pairBound ^ n * d.rho ^ (2 * n * (n - 1)) := by
  simpa only [div_one] using branch_pairs_even_norm_le (S := (1 : ℂ)) (T := a t)
    (A := c t + a t) (by norm_num) (d.angleRoot_continuous ht)
    (edgeAngleRoot_dispersion c a t) (d.root_denominator ht) d.rho_pos.le d.pairBound_pos.le
    (d.root_schur_bound ht) (by simpa only [div_one] using d.pair_bound t ht) n x

theorem pairs_odd_bound {t : ℂ} (ht : t ∈ Metric.closedBall (0 : ℂ) d.radius)
    (n : ℕ) (x : Fin (2 * n + 1) → ℝ) :
    ‖∏ ij ∈ indexPairs (2 * n + 1), branchCanceledPair (a t) (edgeAngleRoot c a t) (x ij.1) (x ij.2)‖ ≤
      (matchingNumber (n + 1) : ℝ) * d.pairBound ^ n * d.rho ^ (2 * n * n) := by
  simpa only [div_one] using branch_pairs_odd_norm_le (S := (1 : ℂ)) (T := a t)
    (A := c t + a t) (by norm_num) (d.angleRoot_continuous ht)
    (edgeAngleRoot_dispersion c a t) (d.root_denominator ht) d.rho_pos d.pairBound_pos
    (d.root_schur_bound ht) (by simpa only [div_one] using d.pair_bound t ht) n x

theorem fullNumerator_bound_of_pairs {N : ℕ} {t : ℂ}
    (ht : t ∈ Metric.closedBall (0 : ℂ) d.radius) (x : Fin N → ℝ) {E : ℝ}
    (hp : ‖∏ ij ∈ indexPairs N,
      branchCanceledPair (a t) (edgeAngleRoot c a t) (x ij.1) (x ij.2)‖ ≤ E) :
    ‖edgeFullNumerator c a t x‖ ≤ (d.prefactorBound * d.bodyBound) ^ N * E := by
  have hbody : ‖∏ i, branchOneBody (edgeAngleRoot c a t) (x i)‖ ≤ d.bodyBound ^ N := by
    simpa only [List.map_ofFn, List.prod_ofFn, List.length_ofFn, Function.comp_def, id_eq] using
      norm_list_prod_le_pow (List.ofFn (id : Fin N → _))
        (fun i => branchOneBody (edgeAngleRoot c a t) (x i)) d.bodyBound_pos.le
        (fun i _ => d.body_bound t ht (x i))
  unfold edgeFullNumerator branchFullNumerator
  rw [norm_mul, norm_mul, norm_pow, mul_pow]
  exact mul_le_mul (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (d.prefactor_bound t ht) N)
    hbody (norm_nonneg _) (pow_nonneg d.prefactorBound_pos.le N)) hp (norm_nonneg _)
    (mul_nonneg (pow_nonneg d.prefactorBound_pos.le N) (pow_nonneg d.bodyBound_pos.le N))

theorem fullNumerator_even_bound {t : ℂ} (ht : t ∈ Metric.closedBall (0 : ℂ) d.radius)
    (n : ℕ) (x : Fin (2 * n) → ℝ) :
    ‖edgeFullNumerator c a t x‖ ≤
      evenMatchedBound (d.prefactorBound * d.bodyBound) d.pairBound d.rho n :=
  d.fullNumerator_bound_of_pairs ht x (d.pairs_even_bound ht n x)

theorem fullNumerator_odd_bound {t : ℂ} (ht : t ∈ Metric.closedBall (0 : ℂ) d.radius)
    (n : ℕ) (x : Fin (2 * n + 1) → ℝ) :
    ‖edgeFullNumerator c a t x‖ ≤
      oddMatchedBound (d.prefactorBound * d.bodyBound) d.pairBound d.rho n :=
  d.fullNumerator_bound_of_pairs ht x (d.pairs_odd_bound ht n x)

theorem half_disk_subset {t : ℂ} (ht : t ∈ Metric.closedBall (0 : ℂ) (d.radius / 2)) :
    Metric.closedBall t (d.radius / 2) ⊆ Metric.closedBall 0 d.radius := by
  apply Metric.closedBall_subset_closedBall'
  have htd := Metric.mem_closedBall.mp ht
  linarith

theorem fullNumerator_even_jet_bound {t : ℂ}
    (ht : t ∈ Metric.closedBall (0 : ℂ) (d.radius / 2))
    (j n : ℕ) (x : Fin (2 * n) → ℝ) :
    ‖iteratedDeriv j (fun u => edgeFullNumerator c a u x) t‖ ≤
      j.factorial * evenMatchedBound (d.prefactorBound * d.bodyBound) d.pairBound d.rho n /
        (d.radius / 2) ^ j := by
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j (half_pos d.radius_pos)
  · apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ (ne_of_gt (half_pos d.radius_pos))]
    intro u hu
    exact (d.fullNumerator_analytic x (d.half_disk_subset ht hu)).differentiableAt.differentiableWithinAt
  · intro u hu
    exact d.fullNumerator_even_bound (d.half_disk_subset ht (Metric.sphere_subset_closedBall hu)) n x

theorem fullNumerator_odd_jet_bound {t : ℂ}
    (ht : t ∈ Metric.closedBall (0 : ℂ) (d.radius / 2))
    (j n : ℕ) (x : Fin (2 * n + 1) → ℝ) :
    ‖iteratedDeriv j (fun u => edgeFullNumerator c a u x) t‖ ≤
      j.factorial * oddMatchedBound (d.prefactorBound * d.bodyBound) d.pairBound d.rho n /
        (d.radius / 2) ^ j := by
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j (half_pos d.radius_pos)
  · apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ (ne_of_gt (half_pos d.radius_pos))]
    intro u hu
    exact (d.fullNumerator_analytic x (d.half_disk_subset ht hu)).differentiableAt.differentiableWithinAt
  · intro u hu
    exact d.fullNumerator_odd_bound (d.half_disk_subset ht (Metric.sphere_subset_closedBall hu)) n x

theorem fullNumerator_even_jet_summable {t : ℂ}
    (ht : t ∈ Metric.closedBall (0 : ℂ) (d.radius / 2)) (j : ℕ)
    (x : (n : ℕ) → Fin (2 * n) → ℝ) :
    Summable (fun n : ℕ => iteratedDeriv j (fun u => edgeFullNumerator c a u (x n)) t) := by
  have hs := (summable_evenMatchedBound_polynomial
    (mul_nonneg d.prefactorBound_pos.le d.bodyBound_pos.le) d.pairBound_pos.le
    d.rho_pos.le d.rho_lt_one 0).mul_left ((j.factorial : ℝ) / (d.radius / 2) ^ j)
  simp only [pow_zero, one_mul] at hs
  apply hs.of_norm_bounded
  intro n
  convert d.fullNumerator_even_jet_bound ht j n (x n) using 1
  ring

theorem fullNumerator_odd_jet_summable {t : ℂ}
    (ht : t ∈ Metric.closedBall (0 : ℂ) (d.radius / 2)) (j : ℕ)
    (x : (n : ℕ) → Fin (2 * n + 1) → ℝ) :
    Summable (fun n : ℕ => iteratedDeriv j (fun u => edgeFullNumerator c a u (x n)) t) := by
  have hs := (summable_oddMatchedBound_polynomial
    (mul_nonneg d.prefactorBound_pos.le d.bodyBound_pos.le) d.pairBound_pos.le
    d.rho_pos.le d.rho_lt_one 0).mul_left ((j.factorial : ℝ) / (d.radius / 2) ^ j)
  simp only [pow_zero, one_mul] at hs
  apply hs.of_norm_bounded
  intro n
  convert d.fullNumerator_odd_jet_bound ht j n (x n) using 1
  ring

end RegularEdgeControl
end
end IsingBulk.AnisoF002.RegularTail.C03
