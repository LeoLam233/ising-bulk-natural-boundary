import IsingBulk.AnisoF002.C03.IsotropicFirstLocalIntegral
import IsingBulk.AnisoF002.C03.IsotropicImaginaryPeriod
import IsingBulk.AnisoF002.C03.RegularAmplitudePeriod

/-!
# Nonzero first amplitude in the original constrained-coordinate measure

The exact physical leading integrand is identified with the independently
proved purely imaginary quadratic period. Both physical parities have a
nonzero chart amplitude, with the original factorial and Haar factors.
Only the generic coordinate/period identities from the regular analysis
are used; no regular first-coefficient endpoint is invoked.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter MeasureTheory IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.RegularTail.C03
open IsingBulk.AnisoF002.NegativeHT.Angular
open scoped Topology BigOperators

def isotropicFirstJetScalar (N : ℕ) (α : ℝ) (j : ℕ) : ℂ :=
  isotropicFirstCenterAmplitude N α *
    ((-1 : ℂ) ^ j * (j.factorial : ℂ) * (-Complex.I / (Real.sin α : ℂ) * (N : ℂ)) ^ j)

def isotropicFirstChartAmplitude (n : ℕ) (α : ℝ) (j : ℕ) : ℂ :=
  ∫ q : Fin n → ℝ, isotropicFirstLeadingJet α j (flatConstrainedAngles q)

theorem isotropicFirstLeadingJet_eq_period {n : ℕ} (α : ℝ) (j : ℕ) (q : Fin n → ℝ) :
    isotropicFirstLeadingJet α j (flatConstrainedAngles q) =
      isotropicFirstJetScalar (n + 1) α j *
        quadraticPeriodIntegrand n (j + 1) (2 * ((n + 1 : ℕ) : ℝ))
          (quadrantCurvature (Real.cos α / Real.sin α) 0) (independentChart n q) := by
  rw [quadraticPeriodIntegrand_chart]
  have hd : ((2 * ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) +
      quadrantCurvature (Real.cos α / Real.sin α) 0 *
        ∑ i, (flatConstrainedAngles q i : ℂ) ^ 2 =
      2 * ((n + 1 : ℕ) : ℂ) - Complex.I * (Real.cos α / Real.sin α : ℝ) *
        ∑ i, (flatConstrainedAngles q i : ℂ) ^ 2 := by
    simp only [quadrantCurvature, Complex.ofReal_zero, zero_sub,
      Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_natCast]
    ring
  rw [hd]
  unfold isotropicFirstLeadingJet isotropicFirstJetScalar
  ring

theorem isotropicFirstChartAmplitude_eq_period (n : ℕ) (α : ℝ) (j : ℕ) :
    isotropicFirstChartAmplitude n α j = isotropicFirstJetScalar (n + 1) α j *
      ∫ v, quadraticPeriodIntegrand n (j + 1) (2 * ((n + 1 : ℕ) : ℝ))
        (quadrantCurvature (Real.cos α / Real.sin α) 0) v ∂independentMeasure n := by
  have h := (independentChart_measurePreserving n).integral_comp
    (independentChart n).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (quadraticPeriodIntegrand n (j + 1) (2 * ((n + 1 : ℕ) : ℝ))
      (quadrantCurvature (Real.cos α / Real.sin α) 0))
  simp only [isotropicFirstChartAmplitude, isotropicFirstLeadingJet_eq_period, integral_const_mul, h]

theorem isotropicFirstJetScalar_ne_zero {N : ℕ} (hN : 0 < N) {α : ℝ}
    (hα : 0 < α) (hπ : α < Real.pi) (j : ℕ) :
    isotropicFirstJetScalar N α j ≠ 0 := by
  have hs : (Real.sin α : ℂ) ≠ 0 := by exact_mod_cast (Real.sin_pos_of_pos_of_lt_pi hα hπ).ne'
  have hn : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  exact mul_ne_zero (isotropicFirstCenterAmplitude_ne_zero hα hπ)
    (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
      (by exact_mod_cast j.factorial_ne_zero))
      (pow_ne_zero _ (mul_ne_zero (div_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hs) hn)))

theorem isotropicFirstChartAmplitude_odd_ne_zero {n : ℕ} (hn0 : 0 < n)
    (hn : Odd (n + 1)) {α : ℝ} (hα : 0 < α) (hhalf : α < Real.pi / 2) :
    isotropicFirstChartAmplitude n α (oddTopOrder (n + 1)) ≠ 0 := by
  have hπ : α < Real.pi := hhalf.trans (by linarith [Real.pi_pos])
  have hcos := Real.cos_pos_of_mem_Ioo (show α ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) from
    ⟨by linarith [Real.pi_pos], hhalf⟩)
  have hcot := div_pos hcos (Real.sin_pos_of_pos_of_lt_pi hα hπ)
  obtain ⟨k, hk⟩ := hn
  have hn' : n = 2 * k := by omega
  have hk0 : 0 < k := by omega
  subst n
  rw [isotropicFirstChartAmplitude_eq_period, oddTopOrder_twice]
  apply mul_ne_zero (isotropicFirstJetScalar_ne_zero (by omega) hα hπ _)
  simpa only [Nat.add_zero] using imaginary_quadraticPeriod_integer_ne_zero
    (by omega : 0 < 2 * k) (radialShape_even_dimension hk0) 0
    (by positivity : 0 < 2 * ((2 * k + 1 : ℕ) : ℝ)) hcot

theorem isotropicFirstChartAmplitude_even_ne_zero {n : ℕ} (hn : Even (n + 1))
    {α : ℝ} (hα : 0 < α) (hhalf : α < Real.pi / 2) :
    isotropicFirstChartAmplitude n α (evenTopOrder (n + 1)) ≠ 0 := by
  have hn0 : 0 < n := by obtain ⟨k, hk⟩ := hn; omega
  have hπ : α < Real.pi := hhalf.trans (by linarith [Real.pi_pos])
  have hcos := Real.cos_pos_of_mem_Ioo (show α ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) from
    ⟨by linarith [Real.pi_pos], hhalf⟩)
  have hrad : radialPower n = 2 * evenTopOrder (n + 1) := by
    have h := even_first_scaling_degree hn
    unfold radialPower
    omega
  rw [isotropicFirstChartAmplitude_eq_period]
  apply mul_ne_zero (isotropicFirstJetScalar_ne_zero (by omega) hα hπ _)
  exact imaginary_quadraticPeriod_half_integer_ne_zero hn0 hrad (by positivity)
    (div_pos hcos (Real.sin_pos_of_pos_of_lt_pi hα hπ))

end
end IsingBulk.AnisoF002.Isotropic
