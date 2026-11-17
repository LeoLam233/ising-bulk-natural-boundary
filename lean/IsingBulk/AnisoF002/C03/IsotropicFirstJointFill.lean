import IsingBulk.AnisoF002.C03.IsotropicFirstAmplitude
import IsingBulk.AnisoF002.C03.IsotropicFirstCompactDirections

/-!
# Joint complex analyticity of the actual first-denominator filling

All angular directions vary together with the scale and the temperature.
This allows compactness to bound the actual differentiated quotient in
every weighted direction, while retaining the Vandermonde separately.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem isotropicFirstBlowupDenominator_analytic_parameter {N : ℕ} {α : ℝ}
    (hα : 0 < α) (hπ : α < Real.pi) {p : E} {s t : E → ℂ} {x : E → Fin N → ℂ}
    (hs : AnalyticAt ℂ s p) (ht : AnalyticAt ℂ t p)
    (hx : ∀ i, AnalyticAt ℂ (fun q => x q i) p) (hs0 : s p = 0) :
    AnalyticAt ℂ (fun q => isotropicFirstBlowupDenominator α (x q) (s q, t q)) p := by
  have hB (i : Fin N) : AnalyticAt ℂ (fun q =>
      isotropicFirstQuadraticIncrement α (x q i) (s q, t q)) p := by
    have hsin : AnalyticAt ℂ (fun q => complexSinc (s q * x q i / 2)) p :=
      (complexSinc_analyticAt _).comp ((hs.mul (hx i)).div_const)
    have hfill := (isotropicSecondFill_analytic Complex.analyticAt_sin).comp_of_eq
      (hs.mul (hx i)) (by change s p * x p i = 0; rw [hs0, zero_mul])
    exact (ht.add (((analyticAt_const.mul ((hx i).pow 2)).div_const).mul (hsin.pow 2))).sub
      ((analyticAt_const.mul ((hx i).pow 2)).mul hfill)
  have hA (i : Fin N) : AnalyticAt ℂ (fun q =>
      isotropicFirstLinearIncrement α (x q i) (s q, t q)) p :=
    (analyticAt_const.mul (hx i)).add (hs.mul (hB i))
  have hP (i : Fin N) : AnalyticAt ℂ (fun q =>
      isotropicFirstBlowupPhase α (x q i) (s q, t q)) p := by
    have hfill := (isotropicSecondFill_analytic (isotropic_first_scalar_phase_jets hα hπ).1).comp_of_eq
      (analyticAt_const.add (hs.mul (hA i)))
      (by change (Real.cos α : ℂ) + s p * _ = _; rw [hs0, zero_mul, add_zero])
    exact (analyticAt_const.mul (hB i)).add (((hA i).pow 2).mul hfill)
  have hsum : AnalyticAt ℂ (fun q => isotropicFirstBlowupTotal α (x q) (s q, t q)) p :=
    Finset.univ.analyticAt_fun_sum fun i _ => hP i
  have he := isotropicExpFill_analytic_zero.comp_of_eq ((hs.pow 2).mul hsum).neg
    (by change -(s p ^ 2 * _) = 0; rw [hs0, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul, neg_zero])
  exact hsum.mul he

def isotropicFirstFilledRatio {N : ℕ} (α : ℝ) (σ : ℂ) (x : Fin N → ℂ)
    (p : ℂ × ℂ) : ℂ :=
  isotropicFirstAmplitude α σ (p.1 ^ 2 * p.2, fun i => p.1 * x i) /
    isotropicFirstBlowupDenominator α x p

theorem isotropicFirstFilledRatio_analytic_parameter {N : ℕ} {α : ℝ}
    (hα : 0 < α) (hπ : α < Real.pi) (σ : ℂ) {p : E}
    {s t : E → ℂ} {x : E → Fin N → ℂ}
    (hs : AnalyticAt ℂ s p) (ht : AnalyticAt ℂ t p)
    (hx : ∀ i, AnalyticAt ℂ (fun q => x q i) p) (hs0 : s p = 0)
    (hq : isotropicFirstBlowupDenominator α (x p) (s p, t p) ≠ 0) :
    AnalyticAt ℂ (fun q => isotropicFirstFilledRatio α σ (x q) (s q, t q)) p := by
  have hm : AnalyticAt ℂ (fun q => (s q ^ 2 * t q, fun i => s q * x q i)) p :=
    ((hs.pow 2).mul ht).prod (AnalyticAt.pi fun i => hs.mul (hx i))
  have ha := (isotropicFirstAmplitude_analyticAt (N := N) hα hπ σ).comp_of_eq hm
    (by simp only [hs0, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul, Pi.zero_def])
  exact ha.div (isotropicFirstBlowupDenominator_analytic_parameter hα hπ hs ht hx hs0) hq

def isotropicFirstDirectionalRatio {N : ℕ} (α : ℝ) (σ : ℂ)
    (q : ℂ × (ℂ × (ℂ × (Fin N → ℂ)))) : ℂ :=
  isotropicFirstFilledRatio α σ q.2.2.2
    (q.2.1, q.2.2.1 * isotropicRadialIncrement α (q.2.1 ^ 2 * q.2.2.1) + q.1)

theorem isotropicFirstDirectionalRatio_analytic {N : ℕ} (hN : 0 < N) {α : ℝ}
    (hα : 0 < α) (hhalf : α < Real.pi / 2) (σ : ℂ)
    {p : ℝ × (Fin N → ℝ)} (hp : p ∈ isotropicFirstDirections N) :
    AnalyticAt ℂ (isotropicFirstDirectionalRatio α σ)
      (0, (0, ((p.1 : ℂ), fun i => (p.2 i : ℂ)))) := by
  let z : ℂ × (ℂ × (ℂ × (Fin N → ℂ))) :=
    (0, (0, ((p.1 : ℂ), fun i => (p.2 i : ℂ))))
  have hs : AnalyticAt ℂ (fun q : ℂ × (ℂ × (ℂ × (Fin N → ℂ))) => q.2.1) z :=
    analyticAt_fst.comp_of_eq analyticAt_snd rfl
  have hw : AnalyticAt ℂ (fun q : ℂ × (ℂ × (ℂ × (Fin N → ℂ))) => q.2.2.1) z :=
    analyticAt_fst.comp_of_eq (analyticAt_snd.comp_of_eq analyticAt_snd rfl) rfl
  have hx (i : Fin N) : AnalyticAt ℂ
      (fun q : ℂ × (ℂ × (ℂ × (Fin N → ℂ))) => q.2.2.2 i) z := by
    have hv : AnalyticAt ℂ (fun q : ℂ × (ℂ × (ℂ × (Fin N → ℂ))) => q.2.2.2) z :=
      analyticAt_snd.comp_of_eq (analyticAt_snd.comp_of_eq analyticAt_snd rfl) rfl
    exact (show (Fin N → ℂ) →L[ℂ] ℂ from ContinuousLinearMap.proj i).analyticAt _ |>.comp hv
  have ht : AnalyticAt ℂ (fun q : ℂ × (ℂ × (ℂ × (Fin N → ℂ))) =>
      q.2.2.1 * isotropicRadialIncrement α (q.2.1 ^ 2 * q.2.2.1) + q.1) z :=
    (hw.mul ((isotropicRadialIncrement_analytic α).comp_of_eq ((hs.pow 2).mul hw)
      (by change (0 : ℂ) ^ 2 * (p.1 : ℂ) = 0; simp))).add analyticAt_fst
  have hπ : α < Real.pi := hhalf.trans (by linarith [Real.pi_pos])
  have hcos := Real.cos_pos_of_mem_Ioo (show α ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) from
    ⟨by linarith [Real.pi_pos], hhalf⟩)
  have hc : 0 < min (2 * (N : ℝ)) (Real.cos α / Real.sin α) / 2 :=
    div_pos (lt_min (by positivity) (div_pos hcos (Real.sin_pos_of_pos_of_lt_pi hα hπ))) (by norm_num)
  have hq : isotropicRadialShapeFilled α (0, p) ≠ 0 :=
    norm_pos_iff.mp (hc.trans_le (isotropic_first_direction_margin hN hα hhalf hp))
  apply isotropicFirstFilledRatio_analytic_parameter hα hπ σ hs ht hx rfl
  simpa only [z, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul, add_zero,
    isotropicRadialShapeFilled, Complex.ofReal_zero, isotropicRadialFilledDenominator] using hq

end
end IsingBulk.AnisoF002.Isotropic
