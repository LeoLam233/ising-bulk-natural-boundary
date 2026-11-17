import IsingBulk.AnisoF002.C03.NegativeInnerMeasurableRemainder
import IsingBulk.AnisoF002.C03.NegativePhysicalCoefficient

/-!
# The genuine inner real-cycle remainder integral

The fixed angular cutoff is applied to the original constrained angles.
The integral uses the original independent-coordinate Lebesgue measure.
Its angular volume cancels exactly against W_N, leaving the physical
factorial and the all-particle Gaussian estimate.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter MeasureTheory IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology Classical

theorem angularShortSquare_zero (n : ℕ) : angularShortSquare (0 : Fin n → ℝ) = 0 := by
  simp [angularShortSquare, unsignedShortAngle]

def innerAngularClip (n : ℕ) (s : ℝ) (q : Fin n → ℝ) : Fin n → ℝ :=
  if angularShortSquare q ≤ s then q else 0

theorem innerAngularClip_mem (n : ℕ) {s : ℝ} (hs : 0 ≤ s) (q : Fin n → ℝ) :
    angularShortSquare (innerAngularClip n s q) ≤ s := by
  unfold innerAngularClip
  split_ifs with h
  · exact h
  · simpa only [angularShortSquare_zero] using hs

def innerAngularRetraction (n : ℕ) {s : ℝ} (hs : 0 ≤ s) (q : Fin n → ℝ) : InnerAngularSet n s :=
  ⟨innerAngularClip n s q, innerAngularClip_mem n hs q⟩

theorem innerAngularRetraction_measurable (n : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    Measurable (innerAngularRetraction n hs) := by
  have hm : Measurable (innerAngularClip n s) :=
    Measurable.ite (measurableSet_le (angularShortSquare_continuous n).measurable measurable_const)
      measurable_id measurable_const
  exact hm.subtype_mk

namespace InnerRemainderFamily

variable {b B : ℂ → ℂ} {φ r s M kappa : ℝ} {N : ℕ}
  (d : InnerRemainderFamily b B φ N r s M kappa)

def realCycleRemainderDensity (hs : 0 ≤ s) (t : ℂ) (q : Fin N → ℝ) : ℂ :=
  if angularShortSquare q ≤ s then d.remainder t (innerAngularRetraction N hs q) else 0

theorem realCycleRemainderDensity_measurable (hs : 0 ≤ s) :
    Measurable (Function.uncurry (d.realCycleRemainderDensity hs)) := by
  have hc : MeasurableSet {p : ℂ × (Fin N → ℝ) | angularShortSquare p.2 ≤ s} :=
    measurableSet_le ((angularShortSquare_continuous N).measurable.comp measurable_snd) measurable_const
  have hm := d.remainder_measurable.comp
    (measurable_fst.prodMk ((innerAngularRetraction_measurable N hs).comp measurable_snd))
  exact Measurable.ite hc hm measurable_const

theorem realCycleRemainderDensity_analytic (hs : 0 ≤ s) (q : Fin N → ℝ) :
    AnalyticOnNhd ℂ (fun t => d.realCycleRemainderDensity hs t q) (Metric.ball 0 (r / (N : ℝ))) := by
  by_cases hq : angularShortSquare q ≤ s
  · simpa only [realCycleRemainderDensity, hq, ↓reduceIte] using
      d.remainder_analytic (innerAngularRetraction N hs q)
  · simpa only [realCycleRemainderDensity, hq, ↓reduceIte] using analyticOnNhd_const

theorem realCycleRemainderDensity_bound (hs : 0 ≤ s) (hM : 0 ≤ M)
    (q : Fin N → ℝ) {t : ℂ} (ht : t ∈ Metric.ball (0 : ℂ) (r / (4 * (N : ℝ)))) :
    ‖d.realCycleRemainderDensity hs t q‖ ≤
      M * Real.exp (-kappa * (N : ℝ) ^ 2) / ‖windingNormalization N‖ := by
  by_cases hq : angularShortSquare q ≤ s
  · simpa only [realCycleRemainderDensity, hq, ↓reduceIte] using
      d.remainder_bound (innerAngularRetraction N hs q) t ht
  · simp only [realCycleRemainderDensity, hq, ↓reduceIte, norm_zero]
    positivity

end InnerRemainderFamily

def innerCycleRemainder {b B : ℂ → ℂ} {φ r s M kappa : ℝ} {n : ℕ}
    (d : InnerRemainderFamily b B φ (n + 1) r s M kappa) (hs : 0 ≤ s) (t : ℂ) : ℂ :=
  ∫ q in regularAngularBox n, d.realCycleRemainderDensity hs t (negativeConstrainedAngles q)

theorem windingNormalization_norm_succ (n : ℕ) :
    ‖windingNormalization (n + 1)‖ = ((n + 1).factorial : ℝ) * (2 * Real.pi) ^ n := by
  simp only [windingNormalization, Nat.add_sub_cancel, norm_mul, norm_natCast, norm_pow,
    Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]

theorem measurable_parameter_pullback {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {F : ℂ → X → ℂ} {g : Y → X}
    (hF : Measurable (Function.uncurry F)) (hg : Measurable g) :
    Measurable (fun p : ℂ × Y => F p.1 (g p.2)) :=
  hF.comp (measurable_fst.prodMk (hg.comp measurable_snd))

set_option maxHeartbeats 1000000 in
theorem innerCycleRemainder_analytic_and_bound {b B : ℂ → ℂ} {φ r s M kappa : ℝ} {n : ℕ}
    (d : InnerRemainderFamily b B φ (n + 1) r s M kappa)
    (hr : 0 < r) (hs : 0 ≤ s) (hM : 0 ≤ M) :
    AnalyticOnNhd ℂ (innerCycleRemainder d hs)
      (Metric.ball 0 (r / (16 * (n + 1 : ℕ)))) ∧
      (∀ t ∈ Metric.closedBall (0 : ℂ) (r / (8 * (n + 1 : ℕ))),
        ‖innerCycleRemainder d hs t‖ ≤ M * Real.exp (-kappa * ((n + 1 : ℕ) : ℝ) ^ 2)) ∧
      ∀ j : ℕ,
        ‖iteratedDeriv j (innerCycleRemainder d hs) 0 / (j.factorial : ℂ)‖ ≤
          (M * Real.exp (-kappa * ((n + 1 : ℕ) : ℝ) ^ 2)) /
            (r / (64 * (n + 1 : ℕ))) ^ j := by
  let μ : Measure (Fin n → ℝ) := volume.restrict (regularAngularBox n)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (by
    rw [regularAngularBox_volume]
    exact ENNReal.ofReal_ne_top)
  have hmass : μ.real univ = (2 * Real.pi) ^ n := by
    simp only [μ, Measure.real, Measure.restrict_apply_univ, regularAngularBox_volume,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ (2 * Real.pi) ^ n)]
  let F : ℂ → (Fin n → ℝ) → ℂ := fun t q =>
    d.realCycleRemainderDensity hs t (negativeConstrainedAngles q)
  let R : ℝ := r / (8 * (n + 1 : ℕ))
  let E : ℝ := M * Real.exp (-kappa * ((n + 1 : ℕ) : ℝ) ^ 2) / ‖windingNormalization (n + 1)‖
  have hR : 0 < R := by dsimp [R]; positivity
  have hmes : Measurable (Function.uncurry F) := by
    change Measurable (fun p : ℂ × (Fin n → ℝ) =>
      d.realCycleRemainderDensity hs p.1 (negativeConstrainedAngles p.2))
    exact measurable_parameter_pullback (d.realCycleRemainderDensity_measurable hs)
      (negativeConstrainedAngles_continuous n).measurable
  have hsub : Metric.closedBall (0 : ℂ) R ⊆ Metric.ball 0 (r / (4 * (n + 1 : ℕ))) :=
    Metric.closedBall_subset_ball (by
      dsimp [R]
      apply div_lt_div_of_pos_left hr (by positivity)
      nlinarith [show (0 : ℝ) < ((n + 1 : ℕ) : ℝ) by positivity])
  have hsub' : Metric.closedBall (0 : ℂ) R ⊆ Metric.ball 0 (r / (n + 1 : ℕ)) :=
    Metric.closedBall_subset_ball (by
      dsimp [R]
      apply div_lt_div_of_pos_left hr (by positivity)
      nlinarith [show (0 : ℝ) < ((n + 1 : ℕ) : ℝ) by positivity])
  have ha (q : Fin n → ℝ) : AnalyticOnNhd ℂ (fun t => F t q) (Metric.closedBall 0 R) :=
    (d.realCycleRemainderDensity_analytic hs (negativeConstrainedAngles q)).mono hsub'
  have hb' (q : Fin n → ℝ) (t : ℂ) (ht : t ∈ Metric.closedBall (0 : ℂ) R) : ‖F t q‖ ≤ E :=
    d.realCycleRemainderDensity_bound hs hM (negativeConstrainedAngles q) (hsub ht)
  obtain ⟨hIa, hIb⟩ := analytic_integral_of_measurable_analytic_disk (μ := μ) hR hmes ha hb'
  have hnorm : E * μ.real univ ≤ M * Real.exp (-kappa * ((n + 1 : ℕ) : ℝ) ^ 2) := by
    rw [hmass]
    dsimp [E]
    rw [windingNormalization_norm_succ]
    have hp : (0 : ℝ) < (2 * Real.pi) ^ n := by positivity
    have heq : (M * Real.exp (-kappa * ((n + 1 : ℕ) : ℝ) ^ 2) /
        (((n + 1).factorial : ℝ) * (2 * Real.pi) ^ n)) * (2 * Real.pi) ^ n =
        M * Real.exp (-kappa * ((n + 1 : ℕ) : ℝ) ^ 2) / ((n + 1).factorial : ℝ) := by field_simp
    rw [heq]
    exact div_le_self (by positivity) (by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos (n + 1)))
  refine ⟨?_, ?_, ?_⟩
  · have hrad : r / (16 * (n + 1 : ℕ)) = R / 2 := by dsimp [R]; ring
    rw [hrad]
    exact hIa
  · intro t ht
    exact (hIb t ht).trans hnorm
  · intro j
    have hj := measurable_analytic_integral_normalized_jets (μ := μ) hR hmes ha hb' j
    have hb'' := hj.trans (div_le_div_of_nonneg_right hnorm (by positivity : 0 ≤ (R / 8) ^ j))
    have hrad : r / (64 * (n + 1 : ℕ)) = R / 8 := by dsimp [R]; ring
    rw [hrad]
    exact hb''

end
end IsingBulk.AnisoF002.NegativeHT
