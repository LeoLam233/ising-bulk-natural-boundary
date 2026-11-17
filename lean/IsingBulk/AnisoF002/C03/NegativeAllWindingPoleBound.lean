import IsingBulk.AnisoF002.C03.NegativeAllWindingExpansion
import IsingBulk.AnisoF002.C03.NegativeInnerAngularCut

/-!
# Sharp location of every sufficiently small real-cycle pole

The pole is arbitrary subject to the actual full phase equation.  Thus
the estimate applies to every winding sector and to the same pole used
in exact residue extraction.  No first-winding or zero-sum restriction is
used.  The leading quadratic coefficient is the physical one half.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter
open scoped Topology BigOperators

theorem small_pole_norm_budget {N U Q A M e : ℝ}
    (hN : 1 ≤ N) (hU : 0 ≤ U) (hQ : 0 ≤ Q) (hA : 0 < A) (hM : 0 ≤ M)
    (hUe : U ≤ e) (hQe : Q ≤ e) (he : M * e ≤ A / 8)
    (hb : A * (N * U - Q / 2) ≤ M * (N * U ^ 2 + U * Q + Q ^ 2)) :
    N * U ≤ Q := by
  have hN0 : 0 ≤ N := by linarith
  have hNU : 0 ≤ N * U := mul_nonneg hN0 hU
  have hU2 : U ^ 2 ≤ e * U := by nlinarith
  have hUQ : U * Q ≤ e * U := by nlinarith
  have hQ2 : Q ^ 2 ≤ e * Q := by nlinarith
  have hNU1 : U ≤ N * U := by nlinarith
  have hMe : 0 ≤ M * e := mul_nonneg hM (hU.trans hUe)
  have hb₁ : M * (N * U ^ 2) ≤ (A / 8) * (N * U) := by
    calc
      _ ≤ M * (N * (e * U)) := by gcongr
      _ = (M * e) * (N * U) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right he hNU
  have hb₂ : M * (U * Q) ≤ (A / 8) * (N * U) := by
    calc
      _ ≤ M * (e * U) := mul_le_mul_of_nonneg_left hUQ hM
      _ = (M * e) * U := by ring
      _ ≤ (M * e) * (N * U) := mul_le_mul_of_nonneg_left hNU1 hMe
      _ ≤ _ := mul_le_mul_of_nonneg_right he hNU
  have hb₃ : M * Q ^ 2 ≤ (A / 8) * Q := by
    calc
      _ ≤ M * (e * Q) := mul_le_mul_of_nonneg_left hQ2 hM
      _ = (M * e) * Q := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right he hQ
  nlinarith

theorem real_fourth_sum_le_square (n : ℕ) (v : Fin n → ℝ) :
    (∑ i, ‖(v i : ℂ)‖ ^ 4) ≤ (∑ i, v i ^ 2) ^ 2 := by
  have hh := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
    (f := fun i => v i ^ 2) (fun i _ => sq_nonneg (v i))
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [Complex.norm_real, Real.norm_eq_abs]
  rw [show |v i| ^ 4 = (|v i| ^ 2) ^ 2 by ring, sq_abs]

theorem exists_actual_all_winding_pole_quadratic_bound {B : ℂ → ℂ} {φ : ℝ}
    (hB : AnalyticAt ℂ B 0) (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0) :
    ∃ e K : ℝ, 0 < e ∧ 0 < K ∧ ∀ n : ℕ, 0 < n →
      ∀ v : Fin n → ℝ, ∀ T : ℂ,
        (∑ i, v i ^ 2) ≤ e → ‖T‖ ≤ e →
        (∑ i, negativeGlobalPhase B φ (T, (v i : ℂ))) = (n : ℂ) * ((φ : ℂ) * Complex.I) →
        ‖T - (((∑ i, v i ^ 2) / (2 * (n : ℝ)) : ℝ) : ℂ)‖ ≤
          K * (∑ i, v i ^ 2) ^ 2 / (n : ℝ) ∧
        ((1 / 2 - K * (∑ i, v i ^ 2)) * (∑ i, v i ^ 2)) / (n : ℝ) ≤ ‖T‖ := by
  let g := negativeGlobalPhase B φ
  let a := phaseTemperatureDerivative g (0, 0)
  have hg := negativeGlobalPhase_analyticAt_zero hB hφ hπ
  have hg0 : g (0, 0) = (φ : ℂ) * Complex.I := by
    simpa [g] using negativeGlobalPhase_center B hφ hπ (0 : ℂ)
  have hB0 : B 0 ≠ 0 := by intro h; simp [h] at hBi
  have ha : a ≠ 0 := physical_negative_phase_temperature_derivative_ne_zero
    (Real.sin_pos_of_pos_of_lt_pi hφ hπ).ne' hB hB0 hg hg0
    (Eventually.of_forall (negativeGlobalPhase_cosh B φ))
  have hA : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hsecond : angularJet 2 g (0, 0) = -a := actual_negative_center_second_jet hB hφ hπ hBi
  obtain ⟨r, M, hr, hM, hTaylor⟩ :=
    exists_uniform_all_angle_center_expansion hg (negativeGlobalPhase_even B φ)
  let e := min (r / 2) (min (r ^ 2 / 4) (‖a‖ / (8 * M)))
  let K := 3 * M / ‖a‖
  have he : 0 < e := lt_min (half_pos hr) (lt_min (by positivity) (by positivity))
  have her : e < r := (min_le_left _ _).trans_lt (half_lt_self hr)
  have he2 : e ≤ r ^ 2 / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have heM : M * e ≤ ‖a‖ / 8 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 8 * M)).mp
      ((min_le_right _ _).trans (min_le_right _ _) : e ≤ ‖a‖ / (8 * M))
    nlinarith
  refine ⟨e, K, he, by dsimp [K]; positivity, ?_⟩
  intro n hn v T hQe hTe hzero
  let Q : ℝ := ∑ i, v i ^ 2
  have hQ : 0 ≤ Q := Finset.sum_nonneg fun i _ => sq_nonneg (v i)
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hNpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hN0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have ht : ‖T‖ < r := hTe.trans_lt her
  have hp : (T, (0 : ℂ)) ∈ Metric.ball (0, 0) r := by
    simpa [Metric.mem_ball, dist_eq_norm, Prod.norm_def] using ht
  have hv (i : Fin n) : (T, (v i : ℂ)) ∈ Metric.ball (0, 0) r := by
    have hi : v i ^ 2 ≤ Q := Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
    have hiv : ‖(v i : ℂ)‖ < r := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      nlinarith [sq_abs (v i), abs_nonneg (v i)]
    simpa [Metric.mem_ball, dist_eq_norm, Prod.norm_def] using And.intro ht hiv
  have hTaylor' := hTaylor n T (fun i => (v i : ℂ)) hp hv
  have hg0' : negativeGlobalPhase B φ (0, 0) = (φ : ℂ) * Complex.I := hg0
  have hsecond' : angularJet 2 (negativeGlobalPhase B φ) (0, 0) = -a := hsecond
  rw [hzero, hg0', hsecond'] at hTaylor'
  change ‖(n : ℂ) * ((φ : ℂ) * Complex.I) - (n : ℂ) * ((φ : ℂ) * Complex.I) -
      (n : ℂ) * a * T - (-a / 2) * (∑ i, (v i : ℂ) ^ 2)‖ ≤
      M * ((n : ℝ) * ‖T‖ ^ 2 + ‖T‖ * displacementSquare n (fun i => (v i : ℂ)) +
        ∑ i, ‖(v i : ℂ)‖ ^ 4) at hTaylor'
  have hQcast : (∑ i, (v i : ℂ) ^ 2) = (Q : ℂ) := by simp [Q]
  have hdisp : displacementSquare n (fun i => (v i : ℂ)) = Q := real_displacement_square n v
  rw [hQcast, hdisp] at hTaylor'
  have hnorm : ‖(n : ℂ) * ((φ : ℂ) * Complex.I) - (n : ℂ) * ((φ : ℂ) * Complex.I) -
      (n : ℂ) * a * T - (-a / 2) * (Q : ℂ)‖ =
      ((n : ℝ) * ‖a‖) * ‖T - ((Q / (2 * (n : ℝ)) : ℝ) : ℂ)‖ := by
    have heq : (n : ℂ) * ((φ : ℂ) * Complex.I) - (n : ℂ) * ((φ : ℂ) * Complex.I) -
        (n : ℂ) * a * T - (-a / 2) * (Q : ℂ) =
        -((n : ℂ) * a) * (T - (((Q / (2 * (n : ℝ)) : ℝ) : ℂ))) := by
      push_cast
      field_simp
      ring
    rw [heq, norm_mul, norm_neg, norm_mul, norm_natCast]
  rw [hnorm] at hTaylor'
  have hfour := real_fourth_sum_le_square n v
  have hmain : ((n : ℝ) * ‖a‖) * ‖T - (((Q / (2 * (n : ℝ)) : ℝ) : ℂ))‖ ≤
      M * ((n : ℝ) * ‖T‖ ^ 2 + ‖T‖ * Q + Q ^ 2) := by
    exact hTaylor'.trans (mul_le_mul_of_nonneg_left (by dsimp [Q] at *; linarith) hM.le)
  have hcenter : ‖(((Q / (2 * (n : ℝ)) : ℝ) : ℂ))‖ = Q / (2 * (n : ℝ)) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have htri := norm_sub_norm_le T (((Q / (2 * (n : ℝ)) : ℝ) : ℂ))
  rw [hcenter] at htri
  have hbudget : ‖a‖ * ((n : ℝ) * ‖T‖ - Q / 2) ≤
      M * ((n : ℝ) * ‖T‖ ^ 2 + ‖T‖ * Q + Q ^ 2) := by
    have hh := mul_le_mul_of_nonneg_left htri (mul_nonneg hNpos.le hA.le)
    have heq : ((n : ℝ) * ‖a‖) * (‖T‖ - Q / (2 * (n : ℝ))) =
        ‖a‖ * ((n : ℝ) * ‖T‖ - Q / 2) := by field_simp
    rw [heq] at hh
    exact hh.trans hmain
  have hcoarse := small_pole_norm_budget hN (norm_nonneg T) hQ hA hM.le hTe hQe heM hbudget
  have hU : ‖T‖ ≤ Q / (n : ℝ) := (le_div_iff₀ hNpos).mpr (by simpa [mul_comm] using hcoarse)
  have hU2 : (n : ℝ) * ‖T‖ ^ 2 ≤ Q ^ 2 := by
    have hh := sq_le_sq₀ (by positivity : 0 ≤ (n : ℝ) * ‖T‖) hQ |>.mpr hcoarse
    nlinarith [sq_nonneg ‖T‖]
  have hUQ : ‖T‖ * Q ≤ Q ^ 2 := by
    have hu : ‖T‖ ≤ Q := hU.trans (div_le_self hQ hN)
    nlinarith
  have herror : ‖T - (((Q / (2 * (n : ℝ)) : ℝ) : ℂ))‖ ≤ K * Q ^ 2 / (n : ℝ) := by
    apply (le_div_iff₀ hNpos).mpr
    apply (mul_le_mul_iff_right₀ hA).mp
    have hh := hmain.trans (mul_le_mul_of_nonneg_left (by linarith :
      (n : ℝ) * ‖T‖ ^ 2 + ‖T‖ * Q + Q ^ 2 ≤ 3 * Q ^ 2) hM.le)
    dsimp [K]
    field_simp
    nlinarith
  refine ⟨herror, ?_⟩
  have hl := norm_sub_norm_le (((Q / (2 * (n : ℝ)) : ℝ) : ℂ)) T
  rw [hcenter, norm_sub_rev] at hl
  have h : Q / (2 * (n : ℝ)) - K * Q ^ 2 / (n : ℝ) ≤ ‖T‖ := by linarith
  convert h using 1
  ring

end
end IsingBulk.AnisoF002.NegativeHT
