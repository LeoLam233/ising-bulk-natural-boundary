import IsingBulk.AnisoF002.C03.RegularEdgeNumerator

/-!
# Complete retained-collision jets on the constructed regular-edge disk

This file attaches the fixed sine block to the actual continued complete
numerator, using the chart constants already constructed before N.  The
complementary matching bounds include every internal, cross and remaining
pair.  The resulting particle majorants are summable with every fixed
polynomial loss, uniformly in all real angular tuples.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open IsingBulk.AnisoF002.Isotropic
open scoped BigOperators Topology

def edgeRetainedNumerator {N : ℕ} (m : ℕ) (c a : ℂ → ℂ) (t : ℂ) (x : Fin N → ℝ) : ℂ :=
  edgePrefactor a t ^ N * (∏ i, branchOneBody (edgeAngleRoot c a t) (x i)) *
    ∏ ij ∈ indexPairs N, if ij.1.val < m ∧ ij.2.val < m then
      sinePairCoefficient (a t) (edgeAngleRoot c a t (x ij.1)) (edgeAngleRoot c a t (x ij.2))
    else branchCanceledPair (a t) (edgeAngleRoot c a t) (x ij.1) (x ij.2)

theorem edgeFullNumerator_retained_factorization {N : ℕ} (m : ℕ)
    (c a : ℂ → ℂ) (t : ℂ) (x : Fin N → ℝ) :
    edgeFullNumerator c a t x = embeddedSineBlock m x * edgeRetainedNumerator m c a t x := by
  have he : ∀ ij ∈ indexPairs N,
      branchCanceledPair (a t) (edgeAngleRoot c a t) (x ij.1) (x ij.2) =
        (if ij.1.val < m ∧ ij.2.val < m then
          ((Real.sin ((x ij.1 - x ij.2) / 2) ^ 2 : ℝ) : ℂ) else (1 : ℂ)) *
        (if ij.1.val < m ∧ ij.2.val < m then
          sinePairCoefficient (a t) (edgeAngleRoot c a t (x ij.1)) (edgeAngleRoot c a t (x ij.2))
        else branchCanceledPair (a t) (edgeAngleRoot c a t) (x ij.1) (x ij.2)) := by
    intro ij _
    split_ifs
    · rw [branchCanceledPair_eq_real_sine]
      ring
    · simp
  unfold edgeFullNumerator branchFullNumerator embeddedSineBlock edgeRetainedNumerator
  rw [Finset.prod_congr rfl he, Finset.prod_mul_distrib]
  ring

theorem edgeFullNumerator_iteratedDeriv_retained {N : ℕ} (m j : ℕ)
    (c a : ℂ → ℂ) (t : ℂ) (x : Fin N → ℝ) :
    iteratedDeriv j (fun u => edgeFullNumerator c a u x) t =
      embeddedSineBlock m x * iteratedDeriv j (fun u => edgeRetainedNumerator m c a u x) t := by
  have he : (fun u => edgeFullNumerator c a u x) =
      fun u => embeddedSineBlock m x * edgeRetainedNumerator m c a u x := by
    funext u
    exact edgeFullNumerator_retained_factorization m c a u x
  rw [he, iteratedDeriv_const_mul_field]

theorem twoKernel_retained_pairs_norm_le {m N : ℕ} (P Q : ℝ → ℝ → ℂ)
    (x : Fin (m + N) → ℝ) {D C E : ℝ} (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hQ : ∀ a b : ℝ, ‖Q a b‖ ≤ D) (hP : ∀ a b : ℝ, ‖P a b‖ ≤ C)
    (htail : ‖∏ ij ∈ indexPairs N, P (x (ij.1.natAdd m)) (x (ij.2.natAdd m))‖ ≤ E) :
    ‖∏ ij ∈ indexPairs (m + N), if ij.1.val < m ∧ ij.2.val < m then
      Q (x ij.1) (x ij.2) else P (x ij.1) (x ij.2)‖ ≤ D ^ m.choose 2 * C ^ (m * N) * E := by
  let K : Fin (m + N) → Fin (m + N) → ℂ := fun i j =>
    if i.val < m ∧ j.val < m then Q (x i) (x j) else P (x i) (x j)
  let xs : List (Fin (m + N)) := List.ofFn fun i : Fin m => i.castLE (Nat.le_add_right m N)
  let ys : List (Fin (m + N)) := List.ofFn fun i : Fin N => i.natAdd m
  have hh : ∀ a ∈ xs, ∀ b ∈ xs, ‖K a b‖ ≤ D := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hb
    simpa [K, i.isLt, j.isLt] using hQ (x (i.castLE _)) (x (j.castLE _))
  have hc : ∀ a ∈ xs, ∀ b ∈ ys, ‖K a b‖ ≤ C := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hb
    have hj : ¬ (j.natAdd m).val < m := by simp
    simpa [K, hj] using hP (x (i.castLE _)) (x (j.natAdd m))
  have ht : ‖pairProductOn K ys‖ ≤ E := by
    dsimp [ys]
    rw [pairProductOn_indexPairs]
    have he : ∀ ij ∈ indexPairs N, K (ij.1.natAdd m) (ij.2.natAdd m) =
        P (x (ij.1.natAdd m)) (x (ij.2.natAdd m)) := by
      intro ij _
      simp [K]
    rw [Finset.prod_congr rfl he]
    exact htail
  have hb := pairProductOn_split_norm_le K xs ys hD hC hh hc ht
  have hl : List.ofFn (id : Fin (m + N) → _) = xs ++ ys := List.ofFn_add
  rw [← hl, pairProductOn_indexPairs] at hb
  simpa only [xs, ys, List.length_ofFn, id_eq, K] using hb

namespace RegularEdgeControl
variable {c a : ℂ → ℂ} (d : RegularEdgeControl c a)

theorem sine_parameter_analytic {t : ℂ}
    (ht : t ∈ Metric.closedBall (0 : ℂ) d.radius) (q s : ℝ) :
    AnalyticAt ℂ (fun u => sinePairCoefficient (a u)
      (edgeAngleRoot c a u q) (edgeAngleRoot c a u s)) t :=
  (edgeSineCoefficient_analyticAt (d.coefficient_analytic t ht)
    (d.real_pair_protected ht q s)).comp
      (f := fun u : ℂ => (u, (Real.cos q : ℂ), (Real.cos s : ℂ)))
      (analyticAt_id.prod analyticAt_const)

theorem retainedNumerator_analytic {N : ℕ} (m : ℕ) (x : Fin N → ℝ) {t : ℂ}
    (ht : t ∈ Metric.closedBall (0 : ℂ) d.radius) :
    AnalyticAt ℂ (fun u => edgeRetainedNumerator m c a u x) t := by
  unfold edgeRetainedNumerator
  apply (((d.prefactor_analytic t ht).pow N).mul
    (Finset.univ.analyticAt_fun_prod fun i _ => d.body_parameter_analytic ht (x i))).mul
  apply Finset.analyticAt_fun_prod
  intro ij _
  split_ifs
  · exact d.sine_parameter_analytic ht _ _
  · exact d.pair_parameter_analytic ht _ _

theorem retainedNumerator_bound_of_tail {m N : ℕ} {t : ℂ}
    (ht : t ∈ Metric.closedBall (0 : ℂ) d.radius) (x : Fin (m + N) → ℝ) {E : ℝ}
    (hp : ‖∏ ij ∈ indexPairs N, branchCanceledPair (a t) (edgeAngleRoot c a t)
      (x (ij.1.natAdd m)) (x (ij.2.natAdd m))‖ ≤ E) :
    ‖edgeRetainedNumerator m c a t x‖ ≤
      (d.prefactorBound * d.bodyBound) ^ (m + N) *
        (d.pairBound ^ m.choose 2 * d.pairBound ^ (m * N) * E) := by
  have hbody : ‖∏ i, branchOneBody (edgeAngleRoot c a t) (x i)‖ ≤ d.bodyBound ^ (m + N) := by
    simpa only [List.map_ofFn, List.prod_ofFn, List.length_ofFn, Function.comp_def, id_eq] using
      norm_list_prod_le_pow (List.ofFn (id : Fin (m + N) → _))
        (fun i => branchOneBody (edgeAngleRoot c a t) (x i)) d.bodyBound_pos.le
        (fun i _ => d.body_bound t ht (x i))
  have hpair := twoKernel_retained_pairs_norm_le
    (branchCanceledPair (a t) (edgeAngleRoot c a t))
    (fun q s => sinePairCoefficient (a t) (edgeAngleRoot c a t q) (edgeAngleRoot c a t s))
    x d.pairBound_pos.le d.pairBound_pos.le (d.sine_bound t ht) (d.pair_bound t ht) hp
  unfold edgeRetainedNumerator
  rw [norm_mul, norm_mul, norm_pow, mul_pow]
  exact mul_le_mul (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (d.prefactor_bound t ht) _)
    hbody (norm_nonneg _) (pow_nonneg d.prefactorBound_pos.le _)) hpair (norm_nonneg _)
    (mul_nonneg (pow_nonneg d.prefactorBound_pos.le _) (pow_nonneg d.bodyBound_pos.le _))

theorem retainedNumerator_even_bound {m : ℕ} {t : ℂ}
    (ht : t ∈ Metric.closedBall (0 : ℂ) d.radius) (n : ℕ) (x : Fin (m + 2 * n) → ℝ) :
    ‖edgeRetainedNumerator m c a t x‖ ≤
      ((d.prefactorBound * d.bodyBound) ^ m * d.pairBound ^ m.choose 2) *
        evenMatchedBound ((d.prefactorBound * d.bodyBound) * d.pairBound ^ m)
          d.pairBound d.rho n := by
  have hb := d.retainedNumerator_bound_of_tail ht x
    (d.pairs_even_bound ht n (fun i => x (i.natAdd m)))
  rwa [retained_even_bound_rearrange] at hb

theorem retainedNumerator_odd_bound {m : ℕ} {t : ℂ}
    (ht : t ∈ Metric.closedBall (0 : ℂ) d.radius) (n : ℕ) (x : Fin (m + (2 * n + 1)) → ℝ) :
    ‖edgeRetainedNumerator m c a t x‖ ≤
      ((d.prefactorBound * d.bodyBound) ^ m * d.pairBound ^ m.choose 2) *
        oddMatchedBound ((d.prefactorBound * d.bodyBound) * d.pairBound ^ m)
          d.pairBound d.rho n := by
  have hb := d.retainedNumerator_bound_of_tail ht x
    (d.pairs_odd_bound ht n (fun i => x (i.natAdd m)))
  rwa [retained_odd_bound_rearrange] at hb

theorem retained_full_jet_bound_of_quotient {m N : ℕ} (hm : m ≤ N) {t : ℂ}
    (ht : t ∈ Metric.closedBall (0 : ℂ) (d.radius / 2)) (j : ℕ) (x : Fin N → ℝ) {H : ℝ}
    (hq : ∀ u ∈ Metric.closedBall (0 : ℂ) d.radius, ‖edgeRetainedNumerator m c a u x‖ ≤ H) :
    ‖iteratedDeriv j (fun u => edgeFullNumerator c a u x) t‖ ≤
      retainedSineBlock (fun i : Fin m => x (i.castLE hm)) * (j.factorial * H / (d.radius / 2) ^ j) := by
  have hjet : ‖iteratedDeriv j (fun u => edgeRetainedNumerator m c a u x) t‖ ≤
      j.factorial * H / (d.radius / 2) ^ j := by
    apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j (half_pos d.radius_pos)
    · apply DifferentiableOn.diffContOnCl
      rw [closure_ball _ (ne_of_gt (half_pos d.radius_pos))]
      intro u hu
      exact (d.retainedNumerator_analytic m x
        (d.half_disk_subset ht hu)).differentiableAt.differentiableWithinAt
    · intro u hu
      exact hq u (d.half_disk_subset ht (Metric.sphere_subset_closedBall hu))
  rw [edgeFullNumerator_iteratedDeriv_retained m, norm_mul]
  have h := mul_le_mul_of_nonneg_left hjet (norm_nonneg (embeddedSineBlock m x))
  simpa only [embeddedSineBlock_norm_eq hm] using h

theorem retained_even_jet_majorant (m j k : ℕ) :
    ∃ H : ℕ → ℝ, Summable (fun n : ℕ => ((n : ℝ) + 1) ^ k * H n) ∧
      (∀ n, 0 ≤ H n) ∧ ∀ t ∈ Metric.closedBall (0 : ℂ) (d.radius / 2),
        ∀ n (x : Fin (m + 2 * n) → ℝ),
          ‖iteratedDeriv j (fun u => edgeFullNumerator c a u x) t‖ ≤
            retainedSineBlock (fun i : Fin m => x (i.castLE (Nat.le_add_right m _))) * H n := by
  let A := d.prefactorBound * d.bodyBound
  let K := (j.factorial : ℝ) * (A ^ m * d.pairBound ^ m.choose 2) / (d.radius / 2) ^ j
  let H : ℕ → ℝ := fun n => K * evenMatchedBound (A * d.pairBound ^ m) d.pairBound d.rho n
  have hA : 0 ≤ A := mul_nonneg d.prefactorBound_pos.le d.bodyBound_pos.le
  have hC : 0 ≤ d.pairBound := d.pairBound_pos.le
  have hq : 0 ≤ d.rho := d.rho_pos.le
  have hR : 0 < d.radius / 2 := half_pos d.radius_pos
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hs := (summable_evenMatchedBound_polynomial
    (mul_nonneg hA (pow_nonneg d.pairBound_pos.le m)) d.pairBound_pos.le
      d.rho_pos.le d.rho_lt_one k).mul_left K
  refine ⟨H, ?_, ?_, ?_⟩
  · convert hs using 1
    funext n
    dsimp [H]
    ring
  · intro n
    exact mul_nonneg hK (by unfold evenMatchedBound; positivity)
  · intro t ht n x
    have hh := d.retained_full_jet_bound_of_quotient (Nat.le_add_right m _) ht j x
      (fun u hu => d.retainedNumerator_even_bound hu n x)
    convert hh using 1
    dsimp [H, K, A]
    ring

theorem retained_odd_jet_majorant (m j k : ℕ) :
    ∃ H : ℕ → ℝ, Summable (fun n : ℕ => ((n : ℝ) + 1) ^ k * H n) ∧
      (∀ n, 0 ≤ H n) ∧ ∀ t ∈ Metric.closedBall (0 : ℂ) (d.radius / 2),
        ∀ n (x : Fin (m + (2 * n + 1)) → ℝ),
          ‖iteratedDeriv j (fun u => edgeFullNumerator c a u x) t‖ ≤
            retainedSineBlock (fun i : Fin m => x (i.castLE (Nat.le_add_right m _))) * H n := by
  let A := d.prefactorBound * d.bodyBound
  let K := (j.factorial : ℝ) * (A ^ m * d.pairBound ^ m.choose 2) / (d.radius / 2) ^ j
  let H : ℕ → ℝ := fun n => K * oddMatchedBound (A * d.pairBound ^ m) d.pairBound d.rho n
  have hA : 0 ≤ A := mul_nonneg d.prefactorBound_pos.le d.bodyBound_pos.le
  have hC : 0 ≤ d.pairBound := d.pairBound_pos.le
  have hq : 0 ≤ d.rho := d.rho_pos.le
  have hR : 0 < d.radius / 2 := half_pos d.radius_pos
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hs := (summable_oddMatchedBound_polynomial
    (mul_nonneg hA (pow_nonneg d.pairBound_pos.le m)) d.pairBound_pos.le
      d.rho_pos.le d.rho_lt_one k).mul_left K
  refine ⟨H, ?_, ?_, ?_⟩
  · convert hs using 1
    funext n
    dsimp [H]
    ring
  · intro n
    exact mul_nonneg hK (by unfold oddMatchedBound; positivity)
  · intro t ht n x
    have hh := d.retained_full_jet_bound_of_quotient (Nat.le_add_right m _) ht j x
      (fun u hu => d.retainedNumerator_odd_bound hu n x)
    convert hh using 1
    dsimp [H, K, A]
    ring

end RegularEdgeControl
end
end IsingBulk.AnisoF002.RegularTail.C03
