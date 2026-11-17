import IsingBulk.AnisoF002.C03.IsotropicFirstPeriodAmplitude
import IsingBulk.AnisoF002.C03.RegularCompactIntegral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Exact physical local coefficient and its differentiated measure change

The local coefficient is the original normalized density integrated on
one fixed constrained quadratic shape ball. Joint upper-region analyticity
justifies every temperature derivative. The change u=s v is a proved
Lebesgue-measure identity and retains the full dimension exponent.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter MeasureTheory IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology BigOperators

def isotropicFirstShapeBall (n : ℕ) (ρ : ℝ) : Set (Fin n → ℝ) :=
  {q | angularQuadratic (flatConstrainedAngles q) < ρ}

def isotropicFirstShapeClosedBall (n : ℕ) (ρ : ℝ) : Set (Fin n → ℝ) :=
  {q | angularQuadratic (flatConstrainedAngles q) ≤ ρ}

theorem isotropicFirstShapeBall_measurable (n : ℕ) (ρ : ℝ) :
    MeasurableSet (isotropicFirstShapeBall n ρ) :=
  (isOpen_lt ((angularQuadratic_continuous _).comp (flatConstrainedAngles_continuous n))
    continuous_const).measurableSet

theorem isotropicFirstShapeClosedBall_compact (n : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    IsCompact (isotropicFirstShapeClosedBall n ρ) := by
  have hc : IsClosed (isotropicFirstShapeClosedBall n ρ) :=
    isClosed_le ((angularQuadratic_continuous _).comp (flatConstrainedAngles_continuous n)) continuous_const
  apply (isCompact_closedBall (0 : Fin n → ℝ) (Real.sqrt ρ)).of_isClosed_subset hc
  intro q hq
  rw [Metric.mem_closedBall, dist_zero_right]
  have hh := (flatConstrainedAngles_quadratic_lower q).trans hq
  nlinarith [Real.sq_sqrt hρ, Real.sqrt_nonneg ρ, norm_nonneg q]

def isotropicFirstLocalCoefficient (n : ℕ) (α : ℝ) (σ : ℂ) (ρ : ℝ) (h : ℂ) : ℂ :=
  ∫ q in isotropicFirstShapeBall n ρ,
    isotropicFirstJointDensity α σ (h, complexAngles (flatConstrainedAngles q))

theorem isotropicFirstJointDensity_analytic_inward {N : ℕ} (hN : 0 < N)
    (α : ℝ) (σ : ℂ) (hσ : ‖σ‖ ≤ 1) {h : ℂ} (hh : 0 < h.im) (x : Fin N → ℝ) :
    AnalyticAt ℂ (isotropicFirstJointDensity α σ) (h, complexAngles x) := by
  have hv (i : Fin N) : AnalyticAt ℂ (fun p : ℂ × (Fin N → ℂ) => -(α : ℂ) + p.2 i)
      (h, complexAngles x) :=
    analyticAt_const.add ((show (Fin N → ℂ) →L[ℂ] ℂ from ContinuousLinearMap.proj i).analyticAt _
      |>.comp (f := fun p : ℂ × (Fin N → ℂ) => p.2) analyticAt_snd)
  apply isotropicBarePhysicalDensity_analytic_parameter hN σ hσ
    (S := fun p : ℂ × (Fin N → ℂ) => (2 * Real.cos α : ℂ) + p.1)
    (w := fun p : ℂ × (Fin N → ℂ) => fun i => -(α : ℂ) + p.2 i)
    (analyticAt_const.add analyticAt_fst) hv
  intro i
  have he : -(α : ℂ) + complexAngles x i = ((-α + x i : ℝ) : ℂ) := by push_cast; rfl
  simpa only [isotropicDispersion, he, ← Complex.ofReal_cos,
    Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_im,
    Complex.ofReal_re, show (2 : ℂ).im = 0 from rfl,
    zero_mul, mul_zero, add_zero, zero_add, sub_zero] using hh

theorem isotropicFirstLocalCoefficient_iteratedDeriv (n : ℕ) (α : ℝ) (σ : ℂ)
    (hσ : ‖σ‖ ≤ 1) {ρ : ℝ} (hρ : 0 < ρ) {h : ℂ} (hh : 0 < h.im) (j : ℕ) :
    iteratedDeriv j (isotropicFirstLocalCoefficient n α σ ρ) h =
      ∫ q in isotropicFirstShapeBall n ρ,
        iteratedDeriv j (fun u => isotropicFirstJointDensity α σ
          (u, complexAngles (flatConstrainedAngles q))) h := by
  let K := isotropicFirstShapeClosedBall n ρ
  have hK : IsCompact K := isotropicFirstShapeClosedBall_compact n hρ.le
  have hsub : isotropicFirstShapeBall n ρ ⊆ K := by
    intro q hq
    exact (show angularQuadratic (flatConstrainedAngles q) < ρ from hq).le
  let μ := volume.restrict (isotropicFirstShapeBall n ρ)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr
    ((measure_mono hsub).trans_lt hK.measure_lt_top).ne
  have hμ : ∀ᵐ q ∂μ, q ∈ K :=
    (ae_restrict_mem (isotropicFirstShapeBall_measurable n ρ)).mono hsub
  exact iteratedDeriv_integral_of_joint_analytic (μ := μ)
    (f := isotropicFirstJointDensity α σ)
    (g := fun q : Fin n → ℝ => complexAngles (flatConstrainedAngles q)) hK hμ
    ((complexAngles_continuous _).comp (flatConstrainedAngles_continuous n))
    (fun q _ => isotropicFirstJointDensity_analytic_inward (Nat.succ_pos n) α σ hσ hh
      (flatConstrainedAngles q)) j

theorem isotropicFirstScaledLocal_integral_scaling (n : ℕ) (α : ℝ) (σ : ℂ)
    (j : ℕ) (ρ : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    (∫ q : Fin n → ℝ, isotropicFirstScaledLocal α σ j ρ s q) =
      ((s : ℂ) ^ (2 * j + 2) / (s : ℂ) ^ (2 * (n + 1).choose 2)) / (s : ℂ) ^ n *
        ∫ q in isotropicFirstShapeBall n ρ,
          iteratedDeriv j (fun h => isotropicFirstJointDensity α σ
            (h, complexAngles (flatConstrainedAngles q)))
            (isotropicRadialParameter α (s ^ 2) - (2 * Real.cos α : ℂ)) := by
  let F : (Fin n → ℝ) → ℂ := fun q =>
    if angularQuadratic (flatConstrainedAngles q) < ρ then
      iteratedDeriv j (fun h => isotropicFirstJointDensity α σ
        (h, complexAngles (flatConstrainedAngles q)))
        (isotropicRadialParameter α (s ^ 2) - (2 * Real.cos α : ℂ)) else 0
  have he : (fun q : Fin n → ℝ => isotropicFirstScaledLocal α σ j ρ s q) =
      fun q => ((s : ℂ) ^ (2 * j + 2) / (s : ℂ) ^ (2 * (n + 1).choose 2)) * F (s • q) := by
    funext q
    by_cases hq : angularQuadratic (flatConstrainedAngles (s • q)) < ρ
    · simp only [isotropicFirstScaledLocal, F, ite_eq_left hq, isotropicFirstRealScaledJet]
      congr 2
      funext h
      rw [show s • q = (fun i => s * q i) by rfl, flatConstrainedAngles_mul]
      rfl
    · simp only [isotropicFirstScaledLocal, F, ite_eq_right hq, mul_zero]
  have hF : F = (isotropicFirstShapeBall n ρ).indicator
      (fun q => iteratedDeriv j (fun h => isotropicFirstJointDensity α σ
        (h, complexAngles (flatConstrainedAngles q)))
        (isotropicRadialParameter α (s ^ 2) - (2 * Real.cos α : ℂ))) := by
    funext q
    rfl
  rw [he, integral_const_mul, Measure.integral_comp_smul_of_nonneg volume F s (hR := hs),
    Module.finrank_pi, Fintype.card_fin, Complex.real_smul, Complex.ofReal_inv,
    Complex.ofReal_pow, hF, integral_indicator (isotropicFirstShapeBall_measurable n ρ)]
  ring

theorem isotropicFirstLocalCoefficient_scaled_integral (n : ℕ) {α : ℝ}
    (hα : 0 < α) (hπ : α < Real.pi) (σ : ℂ) (hσ : ‖σ‖ ≤ 1)
    (j : ℕ) {ρ s : ℝ} (hρ : 0 < ρ) (hs : 0 < s) :
    (∫ q : Fin n → ℝ, isotropicFirstScaledLocal α σ j ρ s q) =
      ((s : ℂ) ^ (2 * j + 2) / (s : ℂ) ^ (n + 2 * (n + 1).choose 2)) *
        iteratedDeriv j (isotropicFirstLocalCoefficient n α σ ρ)
          (isotropicRadialParameter α (s ^ 2) - (2 * Real.cos α : ℂ)) := by
  have him : 0 < (isotropicRadialParameter α (s ^ 2) - (2 * Real.cos α : ℂ)).im := by
    simpa only [Complex.sub_im, Complex.mul_im, Complex.ofReal_im,
      Complex.ofReal_re, show (2 : ℂ).im = 0 from rfl,
      mul_zero, zero_mul, add_zero, sub_zero] using
      isotropicRadialParameter_im_pos hα hπ (sq_pos_of_pos hs)
  rw [isotropicFirstScaledLocal_integral_scaling n α σ j ρ hs.le,
    isotropicFirstLocalCoefficient_iteratedDeriv n α σ hσ hρ him j,
    pow_add (s : ℂ) n (2 * (n + 1).choose 2)]
  field_simp

end
end IsingBulk.AnisoF002.Isotropic
