import IsingBulk.AnisoF002.C03.IsotropicObliqueKernel
import IsingBulk.AnisoF002.C03.IsotropicPeriodicIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# One-dimensional coarea for the exact oblique physical phase

This is a change of variable for an actual phase path and its actual
derivative. The periodic logarithmic majorant is integrated after the
change of variable. The lower attenuation may grow with particle number.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology
open Set Metric MeasureTheory

theorem complex_phase_denominator_ne_zero (z : ℂ) (hz : z.im < 0) :
    1 - Complex.exp (-Complex.I * z) ≠ 0 := by
  have hn : ‖Complex.exp (-Complex.I * z)‖ < 1 := by
    rw [Complex.norm_exp]
    have he : (-Complex.I * z).re = z.im := by simp
    rw [he]
    exact Real.exp_lt_one_iff.mpr hz
  intro h
  have he := congrArg norm (sub_eq_zero.mp h)
  rw [norm_one] at he
  linarith only [he, hn]

theorem frozen_oblique_kernel_bound_complex (a₀ : ℝ) (z : ℂ)
    (ha₀ : 0 < a₀) (ha₀1 : a₀ ≤ 1) (hz : a₀ ≤ -z.im) :
    1 / ‖1 - Complex.exp (-Complex.I * z)‖ ≤
      (4 + 2 * Real.pi) * periodicKernel (2 * Real.pi * Real.cos frozenObliqueAngle)
        a₀ (frozenObliqueRotation * z).re := by
  have he : ((z.re : ℂ) - Complex.I * ((-z.im : ℝ) : ℂ)) = z := by
    apply Complex.ext <;> simp
  have hh := frozen_oblique_kernel_bound a₀ (-z.im) z.re ha₀ ha₀1 hz
  rw [he] at hh
  simpa only [periodicKernel, mul_one_div] using hh

theorem particle_attenuation_log_cost (c ε : ℝ) (N : ℕ)
    (hc : 0 < c) (hε : 0 < ε) (hε1 : ε ≤ 1) (hN : 0 < N) :
    1 + |Real.log (min 1 (c * N * ε))| ≤
      (1 + |Real.log c|) * (1 + |Real.log ε|) := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hnpos : (0 : ℝ) < N := by exact_mod_cast hN
  by_cases hcut : 1 ≤ c * N * ε
  · rw [min_eq_left hcut, Real.log_one, abs_zero]
    nlinarith only [abs_nonneg (Real.log c), abs_nonneg (Real.log ε),
      mul_nonneg (abs_nonneg (Real.log c)) (abs_nonneg (Real.log ε))]
  · have hcut' : c * N * ε ≤ 1 := (lt_of_not_ge hcut).le
    have hlogneg : Real.log (c * N * ε) ≤ 0 := Real.log_nonpos (by positivity) hcut'
    rw [min_eq_right hcut', abs_of_nonpos hlogneg,
      Real.log_mul (mul_pos hc hnpos).ne' hε.ne', Real.log_mul hc.ne' hnpos.ne']
    have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hn
    have hlogε : Real.log ε ≤ 0 := Real.log_nonpos hε.le hε1
    rw [abs_of_nonpos hlogε]
    have hp := mul_nonneg (abs_nonneg (Real.log c)) (neg_nonneg.mpr hlogε)
    nlinarith only [hlogN, neg_le_abs (Real.log c), hp]

/-- The exact oblique phase path, actual Jacobian ratio, and attenuation
give the logarithmic fiber integral. Every derivative in this statement
belongs to the supplied phase; no reparameterized model is substituted. -/
theorem exists_oblique_phase_fiber_integral_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (G : ℝ → ℂ) (D F : ℝ → ℝ)
      (A B a₀ Q : ℝ), A ≤ B → 0 < a₀ → a₀ ≤ 1 → 0 ≤ Q →
      Continuous G → Continuous D → Continuous F →
      (∀ t ∈ Icc A B, HasDerivAt (fun u => (frozenObliqueRotation * G u).re) (D t) t) →
      (∀ t ∈ Icc A B, 0 < D t ∧ 0 ≤ F t ∧ F t / D t ≤ Q ∧ a₀ ≤ -(G t).im) →
      (∫ t in A..B, F t / ‖1 - Complex.exp (-Complex.I * G t)‖) ≤
        C * Q * (1 + ((frozenObliqueRotation * G B).re - (frozenObliqueRotation * G A).re)) *
          (1 + |Real.log a₀|) := by
  let p := 2 * Real.pi * Real.cos frozenObliqueAngle
  have hp : 0 < p := mul_pos (mul_pos (by norm_num) Real.pi_pos) frozenObliqueAngle_cos_pos
  obtain ⟨C₀, hC₀, hkernel⟩ := exists_periodicKernel_log_integral_bound p hp
  let K := 4 + 2 * Real.pi
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K * C₀, mul_pos hK hC₀, ?_⟩
  intro G D F A B a₀ Q hAB ha₀ ha₀1 hQ hG hD hF hderiv hdata
  let ν : ℝ → ℝ := fun t => (frozenObliqueRotation * G t).re
  have hν : Continuous ν := Complex.continuous_re.comp (continuous_const.mul hG)
  have hmono : MonotoneOn ν (Icc A B) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc A B) hν.continuousOn
    · intro t ht
      exact (hderiv t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hderiv t (interior_subset ht)).deriv]
      exact (hdata t (interior_subset ht)).1.le
  have hνAB : ν A ≤ ν B := hmono (left_mem_Icc.mpr hAB) (right_mem_Icc.mpr hAB) hAB
  have hden (t : ℝ) (ht : t ∈ Icc A B) : 1 - Complex.exp (-Complex.I * G t) ≠ 0 :=
    complex_phase_denominator_ne_zero (G t) (by linarith only [(hdata t ht).2.2.2, ha₀])
  have hcontden : Continuous (fun t => ‖1 - Complex.exp (-Complex.I * G t)‖) :=
    (continuous_const.sub (Complex.continuous_exp.comp (continuous_const.mul hG))).norm
  have hleft : IntervalIntegrable (fun t => F t / ‖1 - Complex.exp (-Complex.I * G t)‖) volume A B := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hAB]
    exact hF.continuousOn.div hcontden.continuousOn (fun t ht => norm_ne_zero_iff.mpr (hden t ht))
  have hrightcont : Continuous (fun t => (Q * K) * (periodicKernel p a₀ (ν t) * D t)) :=
    continuous_const.mul (((periodicKernel_continuous p a₀ ha₀).comp hν).mul hD)
  have hmain := intervalIntegral.integral_mono_on hAB hleft (hrightcont.intervalIntegrable A B)
    (fun t ht => show F t / ‖1 - Complex.exp (-Complex.I * G t)‖ ≤
        (Q * K) * (periodicKernel p a₀ (ν t) * D t) from by
      have hd := hdata t ht
      have hratio : F t ≤ Q * D t := (div_le_iff₀ hd.1).mp hd.2.2.1
      have hk := frozen_oblique_kernel_bound_complex a₀ (G t) ha₀ ha₀1 hd.2.2.2
      have hpk : 0 ≤ K * periodicKernel p a₀ (ν t) :=
        mul_nonneg hK.le (periodicKernel_nonneg p a₀ (ν t) ha₀)
      calc
        _ = F t * (1 / ‖1 - Complex.exp (-Complex.I * G t)‖) := by ring
        _ ≤ F t * (K * periodicKernel p a₀ (ν t)) := mul_le_mul_of_nonneg_left hk hd.2.1
        _ ≤ (Q * D t) * (K * periodicKernel p a₀ (ν t)) := mul_le_mul_of_nonneg_right hratio hpk
        _ = _ := by ring)
  have hsub : (∫ t in A..B, periodicKernel p a₀ (ν t) * D t) =
      ∫ u in ν A..ν B, periodicKernel p a₀ u := by
    apply intervalIntegral.integral_comp_mul_deriv (f := ν) (f' := D) (g := periodicKernel p a₀)
    · intro t ht
      rw [uIcc_of_le hAB] at ht
      exact hderiv t ht
    · exact hD.continuousOn
    · exact periodicKernel_continuous p a₀ ha₀
  rw [intervalIntegral.integral_const_mul, hsub] at hmain
  have hk := hkernel a₀ ha₀ ha₀1 (ν A) (ν B) hνAB
  calc
    _ ≤ (Q * K) * (∫ u in ν A..ν B, periodicKernel p a₀ u) := hmain
    _ ≤ (Q * K) * (C₀ * (1 + (ν B - ν A)) * (1 + |Real.log a₀|)) :=
      mul_le_mul_of_nonneg_left hk (mul_nonneg hQ hK.le)
    _ = _ := by dsimp [ν]; ring

end IsingBulk.AnisoF002.Isotropic
