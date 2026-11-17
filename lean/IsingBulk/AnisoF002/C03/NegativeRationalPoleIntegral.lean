import IsingBulk.AnisoF002.C03.NegativeMeasurableIntegral

/-!
# Exact Taylor coefficients of a measurable pole integral

The pole positions stay a proved positive distance from zero.  Ordinary
dominated differentiation gives every derivative, with the actual residue
and pole retained.  This lemma is generic measure-theoretic calculus.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem pole_distance_lower {c : ℝ} {P t : ℂ} (hP : c ≤ ‖P‖) (ht : ‖t‖ ≤ c / 2) :
    c / 2 ≤ ‖t - P‖ := by
  have h := norm_sub_norm_le P t
  rw [norm_sub_rev] at h
  linarith

theorem pole_inverse_power_hasDerivAt (A P t : ℂ) (k : ℕ) (hne : t - P ≠ 0) :
    HasDerivAt (fun u : ℂ => A / (u - P) ^ (k + 1))
      (-((k + 1 : ℕ) : ℂ) * A / (t - P) ^ (k + 2)) t := by
  have hd := (hasDerivAt_const t A).div (((hasDerivAt_id t).sub_const P).pow (k + 1))
    (pow_ne_zero _ hne)
  change HasDerivAt (fun u : ℂ => A / (u - P) ^ (k + 1))
    ((0 * (t - P) ^ (k + 1) - A * (((k + 1 : ℕ) : ℂ) * (t - P) ^ k * 1)) /
      ((t - P) ^ (k + 1)) ^ 2) t at hd
  convert hd using 1
  simp only [zero_mul, zero_sub, mul_one, pow_add, pow_one, pow_two]
  field_simp

theorem pole_inverse_power_norm_bound {A P t : ℂ} {c M : ℝ} (hc : 0 < c)
    (hA : ‖A‖ ≤ M) (hP : c ≤ ‖P‖) (ht : ‖t‖ ≤ c / 2) (k : ℕ) :
    ‖A / (t - P) ^ (k + 1)‖ ≤ M / (c / 2) ^ (k + 1) := by
  rw [norm_div, norm_pow]
  exact div_le_div₀ ((norm_nonneg A).trans hA) hA (by positivity) (pow_le_pow_left₀ (by positivity)
    (pole_distance_lower hP ht) _)

theorem integral_pole_power_hasDerivAt {A P : X → ℂ} {c M : ℝ}
    (hc : 0 < c) (hA : Measurable A) (hP : Measurable P)
    (hAb : ∀ x, ‖A x‖ ≤ M) (hPb : ∀ x, c ≤ ‖P x‖)
    (k : ℕ) {t : ℂ} (ht : t ∈ Metric.ball (0 : ℂ) (c / 2)) :
    Integrable (fun x => A x / (t - P x) ^ (k + 1)) μ ∧
      HasDerivAt (fun u : ℂ => ∫ x, A x / (u - P x) ^ (k + 1) ∂μ)
        (-((k + 1 : ℕ) : ℂ) * (∫ x, A x / (t - P x) ^ (k + 2) ∂μ)) t := by
  let F : ℂ → X → ℂ := fun u x => A x / (u - P x) ^ (k + 1)
  let D : ℂ → X → ℂ := fun u x => -((k + 1 : ℕ) : ℂ) * A x / (u - P x) ^ (k + 2)
  have hmF (u : ℂ) : AEStronglyMeasurable (F u) μ :=
    (hA.div ((measurable_const.sub hP).pow_const _)).aestronglyMeasurable
  have hmD (u : ℂ) : AEStronglyMeasurable (D u) μ :=
    ((measurable_const.mul hA).div ((measurable_const.sub hP).pow_const _)).aestronglyMeasurable
  have htNorm : ‖t‖ ≤ c / 2 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using Metric.ball_subset_closedBall ht
  have hFi : Integrable (F t) μ := (integrable_const (M / (c / 2) ^ (k + 1))).mono'
    (hmF t) (Eventually.of_forall fun x => pole_inverse_power_norm_bound hc (hAb x) (hPb x) htNorm k)
  have hDb (x : X) (u : ℂ) (hu : u ∈ Metric.closedBall (0 : ℂ) (c / 2)) :
      ‖D u x‖ ≤ ((k + 1 : ℕ) : ℝ) * M / (c / 2) ^ (k + 2) := by
    have huNorm : ‖u‖ ≤ c / 2 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hu
    have hbound := pole_inverse_power_norm_bound hc (hAb x) (hPb x) huNorm (k + 1)
    dsimp [D]
    rw [mul_div_assoc, norm_mul, norm_neg, norm_natCast]
    calc
      _ ≤ ((k + 1 : ℕ) : ℝ) * (M / (c / 2) ^ (k + 2)) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = _ := by ring
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := D) (bound := fun _ => ((k + 1 : ℕ) : ℝ) * M / (c / 2) ^ (k + 2))
    (Metric.closedBall_mem_nhds_of_mem ht) (Eventually.of_forall hmF) hFi (hmD t)
    (Eventually.of_forall hDb) (integrable_const _) (Eventually.of_forall (fun x u hu => by
      have huNorm : ‖u‖ ≤ c / 2 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hu
      have hn : 0 < ‖u - P x‖ := (half_pos hc).trans_le (pole_distance_lower (hPb x) huNorm)
      exact pole_inverse_power_hasDerivAt (A x) (P x) u k (norm_pos_iff.mp hn)))
  refine ⟨hFi, ?_⟩
  have hdeq : (∫ x, D t x ∂μ) =
      -((k + 1 : ℕ) : ℂ) * (∫ x, A x / (t - P x) ^ (k + 2) ∂μ) := by
    dsimp [D]
    simp_rw [mul_div_assoc]
    exact integral_const_mul _ _
  rw [← hdeq]
  exact hd.2

theorem iteratedDeriv_pole_integral {A P : X → ℂ} {c M : ℝ}
    (hc : 0 < c) (hA : Measurable A) (hP : Measurable P)
    (hAb : ∀ x, ‖A x‖ ≤ M) (hPb : ∀ x, c ≤ ‖P x‖)
    (j : ℕ) {t : ℂ} (ht : t ∈ Metric.ball (0 : ℂ) (c / 2)) :
    iteratedDeriv j (fun u : ℂ => ∫ x, A x / (u - P x) ∂μ) t =
      (-1 : ℂ) ^ j * (j.factorial : ℂ) *
        (∫ x, A x / (t - P x) ^ (j + 1) ∂μ) := by
  induction j generalizing t with
  | zero => simp only [iteratedDeriv_zero, pow_zero, Nat.factorial_zero, Nat.cast_one,
      one_mul, Nat.zero_add, pow_one]
  | succ j ih =>
    have hnear : (fun u : ℂ => iteratedDeriv j (fun v : ℂ => ∫ x, A x / (v - P x) ∂μ) u) =ᶠ[𝓝 t]
        (fun u : ℂ => (-1 : ℂ) ^ j * (j.factorial : ℂ) *
          (∫ x, A x / (u - P x) ^ (j + 1) ∂μ)) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds ht] with u hu
      exact ih hu
    rw [iteratedDeriv_succ, hnear.deriv_eq]
    rw [((integral_pole_power_hasDerivAt (μ := μ) hc hA hP hAb hPb j ht).2.const_mul
      ((-1 : ℂ) ^ j * (j.factorial : ℂ))).deriv]
    rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
    ring

theorem normalized_pole_integral_coefficient {A P : X → ℂ} {c M : ℝ}
    (hc : 0 < c) (hA : Measurable A) (hP : Measurable P)
    (hAb : ∀ x, ‖A x‖ ≤ M) (hPb : ∀ x, c ≤ ‖P x‖) (j : ℕ) :
    iteratedDeriv j (fun t : ℂ => ∫ x, A x / (t - P x) ∂μ) 0 / (j.factorial : ℂ) =
      -(∫ x, A x / (P x) ^ (j + 1) ∂μ) := by
  rw [iteratedDeriv_pole_integral (μ := μ) hc hA hP hAb hPb j
    (Metric.mem_ball_self (half_pos hc))]
  have heq (x : X) : A x / (0 - P x) ^ (j + 1) =
      (-1 : ℂ) ^ (j + 1) * (A x / P x ^ (j + 1)) := by
    rw [zero_sub, neg_pow]
    simp only [div_eq_mul_inv, mul_inv_rev, ← inv_pow, inv_neg_one]
    ring
  simp_rw [heq]
  rw [integral_const_mul]
  have hj : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  have hsign : ((-1 : ℂ) ^ j) ^ 2 = 1 := by rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
  calc
    _ = -(((-1 : ℂ) ^ j) ^ 2) * (∫ x, A x / P x ^ (j + 1) ∂μ) := by
      rw [pow_succ]
      field_simp
    _ = _ := by rw [hsign]; ring

end
end IsingBulk.AnisoF002.NegativeHT
