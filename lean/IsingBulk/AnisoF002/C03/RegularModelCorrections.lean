import IsingBulk.AnisoF002.C03.RegularModelExactLog
import IsingBulk.AnisoF002.C03.RegularModelCauchy

/-!
# Quantitative finite differences of the actual analytic model corrections

The constants are constructed from the genuine B(tau), h(tau), and
normalized tau logarithms.  The estimates are simultaneous in the
particle center and its finite step; the derivative order does not enter
these constants.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology

def actualTemperatureCorrection (n : ℕ) : ℝ :=
  (inverseParticleLogTemperature (n : ℂ)⁻¹).re

theorem actual_model_correction_differences {B : ℂ → ℂ} (hB : AnalyticAt ℂ B 0)
    (hslit : B 0 ∈ Complex.slitPlane) (c s : ℝ) :
    ∃ C R : ℝ, 0 < C ∧ 0 < R ∧
      ∀ n d : ℕ, Odd n → Even d → R ≤ (n : ℝ) + d → (d : ℝ) ≤ ((n : ℝ) + d) / 4 →
        |actualModelRemainder B c s (n + 2 * d) - actualModelRemainder B c s n| ≤
          C * (d : ℝ) * ((n : ℝ) + d) ∧
        |actualModelRemainder B c s (n + 2 * d) - 2 * actualModelRemainder B c s (n + d) +
          actualModelRemainder B c s n| ≤ C * (d : ℝ) ^ 2 ∧
        |actualTemperatureCorrection (n + 2 * d) - actualTemperatureCorrection n| ≤
          C * (d : ℝ) / ((n : ℝ) + d) ^ 3 ∧
        |actualTemperatureCorrection (n + 2 * d) - 2 * actualTemperatureCorrection (n + d) +
          actualTemperatureCorrection n| ≤ C * (d : ℝ) ^ 2 / ((n : ℝ) + d) ^ 4 := by
  obtain ⟨q₂, q₁, q₀, U, hU, _, hR⟩ := actualModelRemainder_analytic_form hB hslit c s
  let E := analyticSquareFill inverseParticleLogTemperature
  have hE : AnalyticAt ℂ E 0 := analyticSquareFill_analytic inverseParticleLogTemperature_analytic
  have he (z : ℂ) : inverseParticleLogTemperature z = z ^ 2 * E z := by
    simpa only [inverseParticleLogTemperature_zero, zero_add] using
      analyticSquareFill_identity
        (analytic_even_deriv_zero inverseParticleLogTemperature_analytic inverseParticleLogTemperature_even) z
  obtain ⟨rU, MU, hrU, hMU, hUa, hUb⟩ := exists_analytic_model_disk hU
  obtain ⟨rE, ME, hrE, hME, hEa, hEb⟩ := exists_analytic_model_disk hE
  let r := min rU rE
  let M := MU + ME
  have hr : 0 < r := lt_min hrU hrE
  have hM : 0 < M := add_pos hMU hME
  have hUr : AnalyticOnNhd ℂ U (Metric.closedBall 0 r) :=
    hUa.mono (Metric.closedBall_subset_closedBall (min_le_left _ _))
  have hEr : AnalyticOnNhd ℂ E (Metric.closedBall 0 r) :=
    hEa.mono (Metric.closedBall_subset_closedBall (min_le_right _ _))
  have hUM (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) r) : ‖U z‖ ≤ M :=
    (hUb z (Metric.closedBall_subset_closedBall (min_le_left _ _) hz)).trans (le_add_of_nonneg_right hME.le)
  have hEM (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) r) : ‖E z‖ ≤ M :=
    (hEb z (Metric.closedBall_subset_closedBall (min_le_right _ _) hz)).trans (le_add_of_nonneg_left hMU.le)
  let C := 1 + 4 * |q₂| + 2 * |q₁| + 256 * M
  let R := max 1 (2 / r)
  have hC : 0 < C := by dsimp [C]; positivity
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨C, R, hC, hRpos, ?_⟩
  intro n d hn hd hlarge hstep
  let x : ℝ := (n : ℝ) + d
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hlarge
  have hx : 0 < x := lt_of_lt_of_le (by norm_num) hx1
  have hxr : 2 / x ≤ r := by
    have hh : 2 / r ≤ x := (le_max_right _ _).trans hlarge
    apply (div_le_iff₀ hx).mpr
    have h := (div_le_iff₀ hr).mp hh
    nlinarith
  have hdR : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hm : Odd (n + d) := hn.add_even hd
  have hp : Odd (n + 2 * d) := hn.add_even (even_two_mul d)
  have hleft : (x : ℂ) - (d : ℂ) = (n : ℂ) := by dsimp [x]; push_cast; ring
  have hmid : (x : ℂ) = ((n + d : ℕ) : ℂ) := by dsimp [x]; push_cast; rfl
  have hright : (x : ℂ) + (d : ℂ) = ((n + 2 * d : ℕ) : ℂ) := by dsimp [x]; push_cast; ring
  have hUdiff := inversePowerComposite_differences 0 hUr hUM hM.le hx hxr hdR hstep
  have hEdiff := inversePowerComposite_differences 2 hEr hEM hM.le hx hxr hdR hstep
  simp only [Complex.ofReal_natCast] at hUdiff hEdiff
  rw [hright, hleft, hmid] at hUdiff
  simp only [inversePowerComposite, pow_zero, one_mul, mul_one] at hUdiff
  rw [hright, hleft, hmid] at hEdiff
  have hR1 : |actualModelRemainder B c s (n + 2 * d) - actualModelRemainder B c s n -
      (4 * q₂ * x * d + 2 * q₁ * d)| ≤ 8 * M * d / x := by
    have hh := (Complex.abs_re_le_norm
      (U ((n + 2 * d : ℕ) : ℂ)⁻¹ - U (n : ℂ)⁻¹)).trans hUdiff.1
    rw [hR _ hp, hR _ hn]
    convert hh using 1
    simp only [Complex.sub_re]
    dsimp [x]
    push_cast
    ring
  have hR2 : |actualModelRemainder B c s (n + 2 * d) - 2 * actualModelRemainder B c s (n + d) +
      actualModelRemainder B c s n - 2 * q₂ * (d : ℝ) ^ 2| ≤ 64 * M * (d : ℝ) ^ 2 / x ^ 2 := by
    have hh := (Complex.abs_re_le_norm
      (U ((n + 2 * d : ℕ) : ℂ)⁻¹ - 2 * U ((n + d : ℕ) : ℂ)⁻¹ + U (n : ℂ)⁻¹)).trans hUdiff.2
    rw [hR _ hp, hR _ hm, hR _ hn]
    convert hh using 1
    norm_num [Complex.add_re, Complex.sub_re, Complex.mul_re]
    ring
  have heq (k : ℕ) : actualTemperatureCorrection k =
      (inversePowerComposite E 2 (k : ℂ)).re := by rw [actualTemperatureCorrection, he]; rfl
  have hE1 : |actualTemperatureCorrection (n + 2 * d) - actualTemperatureCorrection n| ≤
      32 * M * d / x ^ 3 := by
    rw [heq, heq]
    have hh := (Complex.abs_re_le_norm
      (inversePowerComposite E 2 ((n + 2 * d : ℕ) : ℂ) - inversePowerComposite E 2 (n : ℂ))).trans hEdiff.1
    rw [Complex.sub_re] at hh
    convert hh using 1
    ring
  have hE2 : |actualTemperatureCorrection (n + 2 * d) - 2 * actualTemperatureCorrection (n + d) +
      actualTemperatureCorrection n| ≤ 256 * M * (d : ℝ) ^ 2 / x ^ 4 := by
    rw [heq, heq, heq]
    have hh := (Complex.abs_re_le_norm (inversePowerComposite E 2 ((n + 2 * d : ℕ) : ℂ) -
      2 * inversePowerComposite E 2 ((n + d : ℕ) : ℂ) + inversePowerComposite E 2 (n : ℂ))).trans hEdiff.2
    norm_num only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.re_ofNat,
      Complex.im_ofNat, zero_mul, sub_zero] at hh
    convert hh using 1
    ring
  have hCx : 8 * M + 4 * |q₂| + 2 * |q₁| ≤ C := by dsimp [C]; linarith
  have hC2 : 64 * M + 2 * |q₂| ≤ C := by dsimp [C]; nlinarith [abs_nonneg q₂, abs_nonneg q₁]
  have hC3 : 32 * M ≤ C := by dsimp [C]; nlinarith [abs_nonneg q₂, abs_nonneg q₁]
  have hC4 : 256 * M ≤ C := by dsimp [C]; nlinarith [abs_nonneg q₂, abs_nonneg q₁]
  have hi : 1 / x ≤ x := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hx1
    norm_num at hh
    simpa only [one_div] using hh.trans hx1
  refine ⟨?_, ?_, ?_, ?_⟩
  · let L := actualModelRemainder B c s (n + 2 * d) - actualModelRemainder B c s n
    let A := 4 * q₂ * x * d + 2 * q₁ * d
    have hA : |A| ≤ 4 * |q₂| * x * d + 2 * |q₁| * d := by
      calc
        _ ≤ |4 * q₂ * x * d| + |2 * q₁ * d| := abs_add_le _ _
        _ = _ := by simp only [abs_mul, abs_of_nonneg hx.le, abs_of_nonneg hdR]; norm_num
    calc
      |L| = |(L - A) + A| := by congr 1; ring
      _ ≤ |L - A| + |A| := abs_add_le _ _
      _ ≤ 8 * M * d / x + (4 * |q₂| * x * d + 2 * |q₁| * d) := add_le_add hR1 hA
      _ ≤ 8 * M * d * x + (4 * |q₂| * x * d + 2 * |q₁| * d * x) := by
        apply add_le_add
        · convert mul_le_mul_of_nonneg_left hi (show 0 ≤ 8 * M * d by positivity) using 1
          ring
        · exact add_le_add le_rfl (le_mul_of_one_le_right (show 0 ≤ 2 * |q₁| * (d : ℝ) by positivity) hx1)
      _ = (8 * M + 4 * |q₂| + 2 * |q₁|) * d * x := by ring
      _ ≤ C * d * x := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCx hdR) hx.le
  · let L := actualModelRemainder B c s (n + 2 * d) - 2 * actualModelRemainder B c s (n + d) +
      actualModelRemainder B c s n
    calc
      |L| = |(L - 2 * q₂ * (d : ℝ) ^ 2) + 2 * q₂ * (d : ℝ) ^ 2| := by congr 1; ring
      _ ≤ |L - 2 * q₂ * (d : ℝ) ^ 2| + |2 * q₂ * (d : ℝ) ^ 2| := abs_add_le _ _
      _ ≤ 64 * M * (d : ℝ) ^ 2 / x ^ 2 + 2 * |q₂| * (d : ℝ) ^ 2 := by
        have ha : |2 * q₂ * (d : ℝ) ^ 2| = 2 * |q₂| * (d : ℝ) ^ 2 := by
          rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg (sq_nonneg (d : ℝ))]
        rw [ha]
        exact add_le_add hR2 le_rfl
      _ ≤ 64 * M * (d : ℝ) ^ 2 + 2 * |q₂| * (d : ℝ) ^ 2 :=
        add_le_add (div_le_self (show 0 ≤ 64 * M * (d : ℝ) ^ 2 by positivity)
          (by nlinarith : 1 ≤ x ^ 2)) le_rfl
      _ = (64 * M + 2 * |q₂|) * (d : ℝ) ^ 2 := by ring
      _ ≤ C * (d : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hC2 (sq_nonneg _)
  · exact hE1.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC3 hdR)
      (pow_nonneg hx.le 3))
  · exact hE2.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC4 (sq_nonneg _)) (pow_nonneg hx.le 4))

end
end IsingBulk.AnisoF002.NegativeHT
