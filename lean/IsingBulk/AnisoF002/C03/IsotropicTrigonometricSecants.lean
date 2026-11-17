import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Tactic

/-!
# Joint analytic trigonometric divided differences

The actual filled sinc removes the diagonal in the sine and cosine difference
identities. These identities are used below to fill the actual inverse secants
of frozen F002 (7.32), without making a new secant-analyticity assumption.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology
open Filter Set

def complexSinc (z : ℂ) : ℂ := dslope Complex.sin 0 z

@[simp] theorem complexSinc_zero : complexSinc 0 = 1 := by
  simp [complexSinc, Complex.deriv_sin]

theorem complexSinc_mul (z : ℂ) : z * complexSinc z = Complex.sin z := by
  simpa only [complexSinc, sub_zero, Complex.sin_zero, smul_eq_mul] using
    sub_smul_dslope Complex.sin 0 z

theorem complexSinc_analyticAt (z : ℂ) : AnalyticAt ℂ complexSinc z := by
  have hd : DifferentiableOn ℂ (dslope Complex.sin 0) univ :=
    (Complex.differentiableOn_dslope (c := (0 : ℂ)) (s := univ) univ_mem).2
      Complex.differentiable_sin.differentiableOn
  exact hd.analyticAt univ_mem

/-- Filled secant of sine, defined by entire functions in both variables. -/
def sineSecant (a b : ℂ) : ℂ :=
  Complex.cos ((a + b) / 2) * complexSinc ((a - b) / 2)

/-- Negative of the filled secant of cosine. -/
def minusCosineSecant (a b : ℂ) : ℂ :=
  Complex.sin ((a + b) / 2) * complexSinc ((a - b) / 2)

@[simp] theorem sineSecant_self (a : ℂ) : sineSecant a a = Complex.cos a := by
  simp [sineSecant, show (a + a) / 2 = a by ring]

@[simp] theorem minusCosineSecant_self (a : ℂ) :
    minusCosineSecant a a = Complex.sin a := by
  simp [minusCosineSecant, show (a + a) / 2 = a by ring]

theorem sineSecant_difference (a b : ℂ) :
    (a - b) * sineSecant a b = Complex.sin a - Complex.sin b := by
  rw [Complex.sin_sub_sin]
  have h := complexSinc_mul ((a - b) / 2)
  unfold sineSecant
  linear_combination 2 * Complex.cos ((a + b) / 2) * h

theorem minusCosineSecant_difference (a b : ℂ) :
    -(a - b) * minusCosineSecant a b = Complex.cos a - Complex.cos b := by
  rw [Complex.cos_sub_cos]
  have h := complexSinc_mul ((a - b) / 2)
  unfold minusCosineSecant
  linear_combination -2 * Complex.sin ((a + b) / 2) * h

theorem sineSecant_analyticAt (q : ℂ × ℂ) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => sineSecant p.1 p.2) q := by
  exact (Complex.analyticAt_cos.comp
    ((analyticAt_fst.add analyticAt_snd).div_const (c := 2))).mul
      ((complexSinc_analyticAt _).comp
        ((analyticAt_fst.sub analyticAt_snd).div_const (c := 2)))

theorem minusCosineSecant_analyticAt (q : ℂ × ℂ) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => minusCosineSecant p.1 p.2) q := by
  exact (Complex.analyticAt_sin.comp
    ((analyticAt_fst.add analyticAt_snd).div_const (c := 2))).mul
      ((complexSinc_analyticAt _).comp
        ((analyticAt_fst.sub analyticAt_snd).div_const (c := 2)))

/-- The true scalar sine secant, including its diagonal derivative. -/
theorem sineSecant_eq_dslope (a b : ℂ) :
    sineSecant a b = dslope Complex.sin b a := by
  by_cases hab : a = b
  · subst b
    simp [Complex.deriv_sin]
  · apply mul_left_cancel₀ (sub_ne_zero.mpr hab)
    rw [sineSecant_difference]
    simpa only [smul_eq_mul] using (sub_smul_dslope Complex.sin b a).symm

/-- The true negative cosine secant, including its diagonal derivative. -/
theorem minusCosineSecant_eq_dslope (a b : ℂ) :
    minusCosineSecant a b = -dslope Complex.cos b a := by
  by_cases hab : a = b
  · subst b
    simp [Complex.deriv_cos]
  · apply mul_left_cancel₀ (neg_ne_zero.mpr (sub_ne_zero.mpr hab))
    rw [minusCosineSecant_difference]
    simpa only [smul_eq_mul, neg_mul_neg] using (sub_smul_dslope Complex.cos b a).symm

end IsingBulk.AnisoF002.Isotropic
