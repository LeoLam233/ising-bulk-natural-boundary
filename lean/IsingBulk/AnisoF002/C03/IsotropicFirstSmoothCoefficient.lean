import IsingBulk.AnisoF002.C03.IsotropicFirstSmoothCutoff

/-!
# The smooth actual first coefficient and every parameter derivative

The fixed real cutoff is carried as a scalar coordinate of a genuinely
joint analytic family. Compactness proves whole-space integrability and
all-order differentiation; scaling retains the original shape measure.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter MeasureTheory IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology BigOperators

def isotropicFirstSmoothCoefficient (n : ℕ) (α : ℝ) (σ : ℂ) (r : ℝ) (h : ℂ) : ℂ :=
  ∫ q : Fin n → ℝ, isotropicFirstShapeCutoff r q *
    isotropicFirstJointDensity α σ (h, complexAngles (flatConstrainedAngles q))

theorem isotropicFirstSmoothCoefficient_analytic_and_jets (n : ℕ) (α : ℝ) (σ : ℂ)
    (hσ : ‖σ‖ ≤ 1) {r : ℝ} (hr : 0 < r) {h : ℂ} (hh : 0 < h.im) :
    AnalyticAt ℂ (isotropicFirstSmoothCoefficient n α σ r) h ∧
      ∀ j : ℕ,
        Integrable (fun q : Fin n → ℝ => isotropicFirstShapeCutoff r q *
          iteratedDeriv j (fun u => isotropicFirstJointDensity α σ
            (u, complexAngles (flatConstrainedAngles q))) h) ∧
        iteratedDeriv j (isotropicFirstSmoothCoefficient n α σ r) h =
          ∫ q : Fin n → ℝ, isotropicFirstShapeCutoff r q *
            iteratedDeriv j (fun u => isotropicFirstJointDensity α σ
              (u, complexAngles (flatConstrainedAngles q))) h := by
  let K := isotropicFirstShapeClosedBall n (2 * r)
  let H : (Fin n → ℝ) → ℂ × (Fin (n + 1) → ℂ) := fun q =>
    (isotropicFirstShapeCutoff r q, complexAngles (flatConstrainedAngles q))
  let F : ℂ × (ℂ × (Fin (n + 1) → ℂ)) → ℂ := fun p =>
    p.2.1 * isotropicFirstJointDensity α σ (p.1, p.2.2)
  have hK : IsCompact K := isotropicFirstShapeClosedBall_compact n (by positivity)
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hH : Continuous H := (isotropicFirstShapeCutoff_continuous n r).prodMk
    ((complexAngles_continuous _).comp (flatConstrainedAngles_continuous n))
  have hzero (q : Fin n → ℝ) (hq : q ∉ K) : isotropicFirstShapeCutoff r q = 0 := by
    apply isotropicFirstShapeCutoff_zero hr
    exact (lt_of_not_ge hq).le
  have hfamily (T : ℂ) (q : Fin n → ℝ) : F (T, H q) =
      isotropicFirstShapeCutoff r q *
        isotropicFirstJointDensity α σ (T, complexAngles (flatConstrainedAngles q)) := rfl
  have he : isotropicFirstSmoothCoefficient n α σ r =
      fun T => ∫ q, F (T, H q) ∂volume.restrict K := by
    funext T
    unfold isotropicFirstSmoothCoefficient
    simp only [hfamily]
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro q hq
    rw [hzero q hq, zero_mul]
  have ha (q : Fin n → ℝ) (_ : q ∈ K) : AnalyticAt ℂ F (h, H q) := by
    have hmap : AnalyticAt ℂ (fun p : ℂ × (ℂ × (Fin (n + 1) → ℂ)) => (p.1, p.2.2)) (h, H q) :=
      analyticAt_fst.prod (analyticAt_snd.comp analyticAt_snd)
    have hb : AnalyticAt ℂ (fun p : ℂ × (ℂ × (Fin (n + 1) → ℂ)) =>
        isotropicFirstJointDensity α σ (p.1, p.2.2)) (h, H q) := by
      simpa only [Function.comp_def] using
        (AnalyticAt.comp (g := isotropicFirstJointDensity α σ)
          (f := fun p : ℂ × (ℂ × (Fin (n + 1) → ℂ)) => (p.1, p.2.2))
          (x := (h, H q))
          (isotropicFirstJointDensity_analytic_inward (Nat.succ_pos n) α σ hσ hh
            (flatConstrainedAngles q)) hmap)
    exact (analyticAt_fst.comp analyticAt_snd).mul hb
  refine ⟨?_, ?_⟩
  · rw [he]
    exact analyticAt_integral_of_joint_analytic hK (ae_restrict_mem hK.measurableSet) hH ha
  · intro j
    have hjzero (q : Fin n → ℝ) (hq : q ∉ K) :
        iteratedDeriv j (fun T => F (T, H q)) h = 0 := by
      have hh : (fun T => F (T, H q)) = fun _ => 0 := by
        funext T
        rw [hfamily, hzero q hq, zero_mul]
      rw [hh]
      simp
    have hjcont : ContinuousOn (fun q : Fin n → ℝ => iteratedDeriv j (fun T => F (T, H q)) h) K := by
      intro q hq
      exact ((parameterIteratedDeriv_analyticAt (ha q hq) j).continuousAt.comp
        (f := fun x : Fin n → ℝ => (h, H x))
        (continuousAt_const.prodMk hH.continuousAt)).continuousWithinAt
    have hjsupp : Function.support (fun q : Fin n → ℝ =>
        iteratedDeriv j (fun T => F (T, H q)) h) ⊆ K := by
      intro q hq
      by_contra hn
      exact hq (hjzero q hn)
    have hji := (integrableOn_iff_integrable_of_support_subset (μ := volume) hjsupp).mp
      (hjcont.integrableOn_compact (μ := volume) hK)
    have hje := iteratedDeriv_integral_of_joint_analytic (μ := volume.restrict K)
      hK (ae_restrict_mem hK.measurableSet) hH ha j
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hjzero] at hje
    constructor
    · simpa only [hfamily, iteratedDeriv_const_mul_field] using hji
    · rw [he]
      simpa only [hfamily, iteratedDeriv_const_mul_field] using hje

theorem isotropicFirstScaledSmooth_integral_scaling (n : ℕ) (α : ℝ) (σ : ℂ)
    (j : ℕ) (r : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    (∫ q : Fin n → ℝ, isotropicFirstScaledSmooth α σ j r s q) =
      ((s : ℂ) ^ (2 * j + 2) / (s : ℂ) ^ (2 * (n + 1).choose 2)) / (s : ℂ) ^ n *
        ∫ q : Fin n → ℝ, isotropicFirstShapeCutoff r q *
          iteratedDeriv j (fun h => isotropicFirstJointDensity α σ
            (h, complexAngles (flatConstrainedAngles q)))
            (isotropicRadialParameter α (s ^ 2) - (2 * Real.cos α : ℂ)) := by
  let F : (Fin n → ℝ) → ℂ := fun q => isotropicFirstShapeCutoff r q *
    iteratedDeriv j (fun h => isotropicFirstJointDensity α σ
      (h, complexAngles (flatConstrainedAngles q)))
      (isotropicRadialParameter α (s ^ 2) - (2 * Real.cos α : ℂ))
  have he : (fun q : Fin n → ℝ => isotropicFirstScaledSmooth α σ j r s q) =
      fun q => ((s : ℂ) ^ (2 * j + 2) / (s : ℂ) ^ (2 * (n + 1).choose 2)) * F (s • q) := by
    funext q
    simp only [isotropicFirstScaledSmooth, isotropicFirstRealScaledJet, F,
      show flatConstrainedAngles (s • q) = fun i => s * flatConstrainedAngles q i from
        flatConstrainedAngles_mul q s]
    exact mul_left_comm _ _ _
  rw [he, integral_const_mul, Measure.integral_comp_smul_of_nonneg volume F s (hR := hs),
    Module.finrank_pi, Fintype.card_fin, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow]
  ring

theorem isotropicFirstSmoothCoefficient_scaled_integral (n : ℕ) {α : ℝ}
    (hα : 0 < α) (hπ : α < Real.pi) (σ : ℂ) (hσ : ‖σ‖ ≤ 1)
    (j : ℕ) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    (∫ q : Fin n → ℝ, isotropicFirstScaledSmooth α σ j r s q) =
      ((s : ℂ) ^ (2 * j + 2) / (s : ℂ) ^ (n + 2 * (n + 1).choose 2)) *
        iteratedDeriv j (isotropicFirstSmoothCoefficient n α σ r)
          (isotropicRadialParameter α (s ^ 2) - (2 * Real.cos α : ℂ)) := by
  have him : 0 < (isotropicRadialParameter α (s ^ 2) - (2 * Real.cos α : ℂ)).im := by
    simpa only [Complex.sub_im, Complex.mul_im, Complex.ofReal_im,
      Complex.ofReal_re, show (2 : ℂ).im = 0 from rfl,
      mul_zero, zero_mul, add_zero, sub_zero] using
      isotropicRadialParameter_im_pos hα hπ (sq_pos_of_pos hs)
  rw [isotropicFirstScaledSmooth_integral_scaling n α σ j r hs.le,
    (isotropicFirstSmoothCoefficient_analytic_and_jets n α σ hσ hr him).2 j |>.2,
    pow_add (s : ℂ) n (2 * (n + 1).choose 2)]
  field_simp

end
end IsingBulk.AnisoF002.Isotropic
