import IsingBulk.AnisoF002.C03.IsotropicFirstPhaseJets

/-!
# Exact constrained blow-up of the physical isotropic first phase

The literal chart has temperature increment s² t and angle -alpha+s x.
The analytic filling below subtracts only the exact linear shape term.
After the zero-sum constraint its sum is the actual logarithmic product
phase divided by s². Its center retains the purely imaginary curvature.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Filter IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology BigOperators

def isotropicFirstQuadraticIncrement (α : ℝ) (x : ℂ) (p : ℂ × ℂ) : ℂ :=
  p.2 + (Real.cos α : ℂ) * x ^ 2 / 2 * complexSinc (p.1 * x / 2) ^ 2 -
    (Real.sin α : ℂ) * x ^ 2 * isotropicSecondFill Complex.sin 0 (p.1 * x)

def isotropicFirstLinearIncrement (α : ℝ) (x : ℂ) (p : ℂ × ℂ) : ℂ :=
  -(Real.sin α : ℂ) * x + p.1 * isotropicFirstQuadraticIncrement α x p

def isotropicFirstBlowupPhase (α : ℝ) (x : ℂ) (p : ℂ × ℂ) : ℂ :=
  deriv upperEdgePhase (Real.cos α : ℂ) * isotropicFirstQuadraticIncrement α x p +
    isotropicFirstLinearIncrement α x p ^ 2 *
      isotropicSecondFill upperEdgePhase (Real.cos α : ℂ)
        ((Real.cos α : ℂ) + p.1 * isotropicFirstLinearIncrement α x p)

def isotropicFirstBlowupTotal {N : ℕ} (α : ℝ) (x : Fin N → ℂ) (p : ℂ × ℂ) : ℂ :=
  ∑ i, isotropicFirstBlowupPhase α (x i) p

theorem isotropicFirstDispersion_blowup (α : ℝ) (x s t : ℂ) :
    isotropicFirstDispersion α (s ^ 2 * t, s * x) =
      (Real.cos α : ℂ) + s * isotropicFirstLinearIncrement α x (s, t) := by
  have hsin := isotropicSecondFill_exact Complex.sin 0 (s * x)
  simp only [Complex.sin_zero, sub_zero, Complex.deriv_sin, Complex.cos_zero,
    mul_one, zero_add] at hsin
  have hcos := one_sub_cos_filled (s * x)
  simp only [isotropicFirstDispersion, Complex.cos_add, Complex.cos_neg,
    Complex.sin_neg, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    isotropicFirstLinearIncrement, isotropicFirstQuadraticIncrement]
  linear_combination (Real.cos α : ℂ) * hcos - (Real.sin α : ℂ) * hsin

theorem isotropicFirstBlowupPhase_exact {α : ℝ} (hα : 0 < α) (hπ : α < Real.pi)
    (x s t : ℂ) :
    isotropicFirstLogPhase α (s ^ 2 * t, s * x) - (α : ℂ) * Complex.I -
      Complex.I * s * x = s ^ 2 * isotropicFirstBlowupPhase α x (s, t) := by
  obtain ⟨_, hv, hd, _⟩ := isotropic_first_scalar_phase_jets hα hπ
  have hs : (Real.sin α : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sin_pos_of_pos_of_lt_pi hα hπ).ne'
  have hh := isotropicSecondFill_exact upperEdgePhase (Real.cos α : ℂ)
    ((Real.cos α : ℂ) + s * isotropicFirstLinearIncrement α x (s, t))
  rw [hv, hd, add_sub_cancel_left] at hh
  unfold isotropicFirstLogPhase
  rw [isotropicFirstDispersion_blowup]
  rw [hh]
  simp only [isotropicFirstBlowupPhase, hd, isotropicFirstLinearIncrement]
  field_simp
  ring

theorem isotropicFirstBlowupTotal_exact {N : ℕ} {α : ℝ}
    (hα : 0 < α) (hπ : α < Real.pi) (x : Fin N → ℂ) (hx : ∑ i, x i = 0)
    (s t : ℂ) :
    (∑ i, isotropicFirstLogPhase α (s ^ 2 * t, s * x i)) -
      (N : ℂ) * ((α : ℂ) * Complex.I) = s ^ 2 * isotropicFirstBlowupTotal α x (s, t) := by
  have hh := congrArg (fun f : (Fin N → ℂ) => ∑ i, f i)
    (funext fun i => isotropicFirstBlowupPhase_exact hα hπ (x i) s t)
  simpa only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, hx, mul_zero, sub_zero,
    isotropicFirstBlowupTotal] using hh

theorem isotropicFirstQuadraticIncrement_analytic (α : ℝ) (x t : ℂ) :
    AnalyticAt ℂ (isotropicFirstQuadraticIncrement α x) (0, t) := by
  have hsin : AnalyticAt ℂ (fun p : ℂ × ℂ => complexSinc (p.1 * x / 2)) (0, t) :=
    (complexSinc_analyticAt _).comp ((analyticAt_fst.mul analyticAt_const).div_const)
  have hf : AnalyticAt ℂ
      (fun p : ℂ × ℂ => isotropicSecondFill Complex.sin 0 (p.1 * x)) (0, t) :=
    (isotropicSecondFill_analytic Complex.analyticAt_sin).comp_of_eq
      (analyticAt_fst.mul analyticAt_const) (by simp)
  exact (analyticAt_snd.add (analyticAt_const.mul (hsin.pow 2))).sub
    (analyticAt_const.mul hf)

theorem isotropicFirstLinearIncrement_analytic (α : ℝ) (x t : ℂ) :
    AnalyticAt ℂ (isotropicFirstLinearIncrement α x) (0, t) :=
  analyticAt_const.add (analyticAt_fst.mul (isotropicFirstQuadraticIncrement_analytic α x t))

theorem isotropicFirstBlowupPhase_analytic {α : ℝ} (hα : 0 < α) (hπ : α < Real.pi)
    (x t : ℂ) : AnalyticAt ℂ (isotropicFirstBlowupPhase α x) (0, t) := by
  have hB := isotropicFirstQuadraticIncrement_analytic α x t
  have hA := isotropicFirstLinearIncrement_analytic α x t
  have hf := isotropicSecondFill_analytic (isotropic_first_scalar_phase_jets hα hπ).1
  have hcomp : AnalyticAt ℂ (fun p : ℂ × ℂ =>
      isotropicSecondFill upperEdgePhase (Real.cos α : ℂ)
        ((Real.cos α : ℂ) + p.1 * isotropicFirstLinearIncrement α x p)) (0, t) :=
    hf.comp_of_eq (analyticAt_const.add (analyticAt_fst.mul hA)) (by simp)
  exact (analyticAt_const.mul hB).add ((hA.pow 2).mul hcomp)

theorem isotropicFirstBlowupTotal_analytic {N : ℕ} {α : ℝ}
    (hα : 0 < α) (hπ : α < Real.pi) (x : Fin N → ℂ) (t : ℂ) :
    AnalyticAt ℂ (isotropicFirstBlowupTotal α x) (0, t) :=
  Finset.univ.analyticAt_fun_sum fun i _ => isotropicFirstBlowupPhase_analytic hα hπ (x i) t

theorem isotropicFirstBlowupPhase_center {α : ℝ} (hα : 0 < α) (hπ : α < Real.pi)
    (x t : ℂ) :
    isotropicFirstBlowupPhase α x (0, t) =
      -Complex.I / (Real.sin α : ℂ) * t -
        Complex.I * (Real.cos α : ℂ) / (Real.sin α : ℂ) * x ^ 2 := by
  obtain ⟨ha, _, hd, hdd⟩ := isotropic_first_scalar_phase_jets hα hπ
  have hs : (Real.sin α : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sin_pos_of_pos_of_lt_pi hα hπ).ne'
  simp only [isotropicFirstBlowupPhase, isotropicFirstLinearIncrement,
    isotropicFirstQuadraticIncrement, zero_mul, zero_div, complexSinc_zero, one_pow,
    mul_one, isotropicSecondFill_sin_zero, mul_zero, sub_zero, add_zero,
    isotropicSecondFill_center ha, hd, hdd]
  field_simp
  ring

theorem isotropicFirstBlowupTotal_center {N : ℕ} {α : ℝ}
    (hα : 0 < α) (hπ : α < Real.pi) (x : Fin N → ℂ) (t : ℂ) :
    isotropicFirstBlowupTotal α x (0, t) =
      -Complex.I / (Real.sin α : ℂ) * (N : ℂ) * t -
        Complex.I * (Real.cos α : ℂ) / (Real.sin α : ℂ) * ∑ i, x i ^ 2 := by
  simp only [isotropicFirstBlowupTotal, isotropicFirstBlowupPhase_center hα hπ,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum]
  ring

end
end IsingBulk.AnisoF002.Isotropic
