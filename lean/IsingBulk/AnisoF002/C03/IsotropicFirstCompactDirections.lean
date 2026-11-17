import IsingBulk.AnisoF002.C03.IsotropicFirstRadialFill
import Mathlib.Topology.Compactness.Compact

/-!
# Compact weighted directions for the actual isotropic first denominator

The radial scale and the whole real shape share s²=epsilon+Q. The compact
direction set retains every possible ratio epsilon/(epsilon+Q). Exact
continuity of the physical filling gives a common positive denominator
margin; no quadratic normal-form identity is assumed.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology BigOperators

def isotropicFirstDirections (N : ℕ) : Set (ℝ × (Fin N → ℝ)) :=
  (Icc 0 1 ×ˢ Metric.closedBall 0 1) ∩ {p | p.1 + ∑ i, p.2 i ^ 2 = 1}

def isotropicRadialShapeFilled {N : ℕ} (α : ℝ) (q : ℝ × (ℝ × (Fin N → ℝ))) : ℂ :=
  isotropicRadialFilledDenominator α (fun i => (q.2.2 i : ℂ)) (q.2.1 : ℂ) (q.1 : ℂ)

theorem isotropicFirstDirections_compact (N : ℕ) : IsCompact (isotropicFirstDirections N) := by
  apply (isCompact_Icc.prod (isCompact_closedBall (0 : Fin N → ℝ) 1)).inter_right
  exact isClosed_eq (by fun_prop) continuous_const

theorem isotropicRadialShapeFilled_continuousAt {N : ℕ} {α : ℝ}
    (hα : 0 < α) (hπ : α < Real.pi) (p : ℝ × (Fin N → ℝ)) :
    ContinuousAt (isotropicRadialShapeFilled α) (0, p) := by
  let T : (ℝ × (ℝ × (Fin N → ℝ))) → ℂ := fun q =>
    (q.2.1 : ℂ) * isotropicRadialIncrement α ((q.1 : ℂ) ^ 2 * (q.2.1 : ℂ))
  have hscale : ContinuousAt (fun q : ℝ × (ℝ × (Fin N → ℝ)) => (q.1 : ℂ)) (0, p) := by fun_prop
  have hweight : ContinuousAt (fun q : ℝ × (ℝ × (Fin N → ℝ)) => (q.2.1 : ℂ)) (0, p) := by fun_prop
  have hx (i : Fin N) : ContinuousAt (fun q : ℝ × (ℝ × (Fin N → ℝ)) => (q.2.2 i : ℂ)) (0, p) := by fun_prop
  have hT : ContinuousAt T (0, p) :=
    hweight.mul ((isotropicRadialIncrement_analytic α).continuousAt.comp_of_eq
      ((hscale.pow 2).mul hweight) (by simp))
  have hB (i : Fin N) : ContinuousAt (fun q : ℝ × (ℝ × (Fin N → ℝ)) =>
      isotropicFirstQuadraticIncrement α (q.2.2 i : ℂ) ((q.1 : ℂ), T q)) (0, p) := by
    have hsinc : ContinuousAt (fun q : ℝ × (ℝ × (Fin N → ℝ)) =>
        complexSinc ((q.1 : ℂ) * (q.2.2 i : ℂ) / 2)) (0, p) :=
      (complexSinc_analyticAt _).continuousAt.comp ((hscale.mul (hx i)).div_const 2)
    have hfill : ContinuousAt (fun q : ℝ × (ℝ × (Fin N → ℝ)) =>
        isotropicSecondFill Complex.sin 0 ((q.1 : ℂ) * (q.2.2 i : ℂ))) (0, p) :=
      (isotropicSecondFill_analytic Complex.analyticAt_sin).continuousAt.comp_of_eq
        (hscale.mul (hx i)) (by simp)
    exact (hT.add (((continuousAt_const.mul ((hx i).pow 2)).div_const 2).mul (hsinc.pow 2))).sub
      ((continuousAt_const.mul ((hx i).pow 2)).mul hfill)
  have hA (i : Fin N) : ContinuousAt (fun q : ℝ × (ℝ × (Fin N → ℝ)) =>
      isotropicFirstLinearIncrement α (q.2.2 i : ℂ) ((q.1 : ℂ), T q)) (0, p) :=
    (continuousAt_const.mul (hx i)).add (hscale.mul (hB i))
  have hP (i : Fin N) : ContinuousAt (fun q : ℝ × (ℝ × (Fin N → ℝ)) =>
      isotropicFirstBlowupPhase α (q.2.2 i : ℂ) ((q.1 : ℂ), T q)) (0, p) := by
    have hf : ContinuousAt (fun q : ℝ × (ℝ × (Fin N → ℝ)) =>
        isotropicSecondFill upperEdgePhase (Real.cos α : ℂ)
          ((Real.cos α : ℂ) + (q.1 : ℂ) *
            isotropicFirstLinearIncrement α (q.2.2 i : ℂ) ((q.1 : ℂ), T q))) (0, p) :=
      (isotropicSecondFill_analytic (isotropic_first_scalar_phase_jets hα hπ).1).continuousAt.comp_of_eq
        (continuousAt_const.add (hscale.mul (hA i))) (by simp)
    exact (continuousAt_const.mul (hB i)).add (((hA i).pow 2).mul hf)
  let P : (ℝ × (ℝ × (Fin N → ℝ))) → ℂ := fun q =>
    isotropicFirstBlowupTotal α (fun i => (q.2.2 i : ℂ)) ((q.1 : ℂ), T q)
  have hsum : ContinuousAt P (0, p) := tendsto_finsetSum Finset.univ (fun i _ => hP i)
  have he : ContinuousAt (fun q : ℝ × (ℝ × (Fin N → ℝ)) =>
      isotropicExpFill (-((q.1 : ℂ) ^ 2 * P q))) (0, p) :=
    isotropicExpFill_analytic_zero.continuousAt.comp_of_eq (((hscale.pow 2).mul hsum).neg) (by simp)
  exact hsum.mul he

theorem isotropic_first_direction_margin {N : ℕ} (hN : 0 < N) {α : ℝ}
    (hα : 0 < α) (hhalf : α < Real.pi / 2) {p : ℝ × (Fin N → ℝ)}
    (hp : p ∈ isotropicFirstDirections N) :
    min (2 * (N : ℝ)) (Real.cos α / Real.sin α) / 2 ≤
      ‖isotropicRadialShapeFilled α (0, p)‖ := by
  have hπ : α < Real.pi := hhalf.trans (by linarith [Real.pi_pos])
  have hsin := Real.sin_pos_of_pos_of_lt_pi hα hπ
  have hcos := Real.cos_pos_of_mem_Ioo (show α ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) from
    ⟨by linarith [Real.pi_pos], hhalf⟩)
  have hcot : 0 < Real.cos α / Real.sin α := div_pos hcos hsin
  have hNc : (0 : ℝ) < N := by exact_mod_cast hN
  have hq : 0 ≤ ∑ i, p.2 i ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hsum := hp.2
  have hweight := hp.1.1.1
  let z : ℂ := isotropicRadialShapeFilled α (0, p)
  have hz : z = 2 * (N : ℂ) * (p.1 : ℂ) -
      Complex.I * (Real.cos α / Real.sin α : ℝ) * ((∑ i, p.2 i ^ 2 : ℝ) : ℂ) := by
    simpa only [z, isotropicRadialShapeFilled, Complex.ofReal_zero,
      Complex.ofReal_sum, Complex.ofReal_pow] using
      isotropicRadialFilledDenominator_center hα hπ (fun i => (p.2 i : ℂ)) (p.1 : ℂ)
  have hz' : z = ((2 * (N : ℝ) * p.1 : ℝ) : ℂ) -
      ((Real.cos α / Real.sin α * ∑ i, p.2 i ^ 2 : ℝ) : ℂ) * Complex.I := by
    rw [hz]
    push_cast
    ring
  have hre : z.re = 2 * (N : ℝ) * p.1 := by
    rw [hz']
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero]
  have him : z.im = -(Real.cos α / Real.sin α) * ∑ i, p.2 i ^ 2 := by
    rw [hz']
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_sub, neg_mul]
  have hreal := Complex.re_le_norm z
  have himag := (neg_le_abs z.im).trans (Complex.abs_im_le_norm z)
  rw [hre] at hreal
  rw [him] at himag
  have hl := mul_le_mul_of_nonneg_right (min_le_left (2 * (N : ℝ)) (Real.cos α / Real.sin α)) hweight
  have hr := mul_le_mul_of_nonneg_right (min_le_right (2 * (N : ℝ)) (Real.cos α / Real.sin α)) hq
  have hprod := congrArg (fun r : ℝ => min (2 * (N : ℝ)) (Real.cos α / Real.sin α) * r) hsum
  change _ ≤ ‖z‖
  nlinarith

theorem exists_uniform_isotropic_first_direction_margin {N : ℕ} (hN : 0 < N) {α : ℝ}
    (hα : 0 < α) (hhalf : α < Real.pi / 2) :
    ∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧ ∀ s : ℝ, |s| < δ →
      ∀ p ∈ isotropicFirstDirections N, c ≤ ‖isotropicRadialShapeFilled α (s, p)‖ := by
  let c := min (2 * (N : ℝ)) (Real.cos α / Real.sin α) / 4
  have hπ : α < Real.pi := hhalf.trans (by linarith [Real.pi_pos])
  have hcos := Real.cos_pos_of_mem_Ioo (show α ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) from
    ⟨by linarith [Real.pi_pos], hhalf⟩)
  have hc : 0 < c := div_pos (lt_min (by positivity)
    (div_pos hcos (Real.sin_pos_of_pos_of_lt_pi hα hπ))) (by norm_num)
  have hnear : ∀ᶠ s : ℝ in 𝓝 0, ∀ p ∈ isotropicFirstDirections N,
      c < ‖isotropicRadialShapeFilled α (s, p)‖ := by
    apply (isotropicFirstDirections_compact N).eventually_forall_of_forall_eventually
    intro p hp
    apply (isotropicRadialShapeFilled_continuousAt hα hπ p).norm.eventually
    apply Ioi_mem_nhds
    have hh := isotropic_first_direction_margin hN hα hhalf hp
    change 0 < min (2 * (N : ℝ)) (Real.cos α / Real.sin α) / 4 at hc
    dsimp only [c]
    linarith
  obtain ⟨δ, hδ, hh⟩ := Metric.eventually_nhds_iff.mp hnear
  refine ⟨δ, c, hδ, hc, ?_⟩
  intro s hs p hp
  exact (hh (by simpa only [Real.dist_eq, sub_zero] using hs) p hp).le

end
end IsingBulk.AnisoF002.Isotropic
