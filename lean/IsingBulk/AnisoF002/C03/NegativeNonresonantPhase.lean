import IsingBulk.AnisoF002.C03.NegativeInnerPoleData
import IsingBulk.AnisoF002.C03.NegativePoleExtraction

/-!
# Uniform phase separation for every nonresonant particle class

The finite periodic phase gap is derived from the actual exponential
phase.  The inner angular increment comes from the genuine full phase
factorization, uniformly before the particle number.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology BigOperators

theorem exists_actual_inner_phase_increment {B : ℂ → ℂ} {φ : ℝ}
    (hB : AnalyticAt ℂ B 0) (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0) :
    ∃ R s M : ℝ, 0 < R ∧ 0 < s ∧ 0 < M ∧ ∀ n : ℕ, 0 < n →
      ∀ q : Fin n → ℝ, angularShortSquare q ≤ s →
      ∀ t ∈ Metric.closedBall (0 : ℂ) R,
        ‖realPhaseTotal B φ n q t - (n : ℂ) * ((φ : ℂ) * Complex.I)‖ ≤
          M * ((n : ℝ) * ‖t‖ + angularShortSquare q) := by
  obtain ⟨R, s, C, a, hR, hs, hC, _, ha, hdata⟩ := exists_actual_inner_pole_data hB hφ hπ hBi
  let M : ℝ := 3 * ‖a‖ / 2 * (C + 1)
  have haN : 0 < ‖a‖ := norm_pos_iff.mpr ha
  refine ⟨R, s, M, hR, hs, by dsimp [M]; positivity, ?_⟩
  intro n hn q hq t ht
  obtain ⟨d⟩ := hdata n hn
  rw [d.phase_factor q hq t ht, add_sub_cancel_left, norm_mul, norm_mul, norm_natCast]
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hS : 0 ≤ angularShortSquare q := Finset.sum_nonneg fun i _ => sq_nonneg _
  have htri : ‖t - d.pole q‖ ≤ ‖t‖ + C * angularShortSquare q / (n : ℝ) :=
    (norm_sub_le t (d.pole q)).trans (add_le_add le_rfl (d.pole_bound q hq))
  calc
    _ ≤ ((n : ℝ) * (‖t‖ + C * angularShortSquare q / (n : ℝ))) * (3 * ‖a‖ / 2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left htri hnR.le) (d.factor_bounds q hq t ht).2.1
        (norm_nonneg _) (by positivity)
    _ = (3 * ‖a‖ / 2) * ((n : ℝ) * ‖t‖ + C * angularShortSquare q) := by field_simp
    _ ≤ _ := by
      dsimp [M]
      have hh : (n : ℝ) * ‖t‖ + C * angularShortSquare q ≤
          (C + 1) * ((n : ℝ) * ‖t‖ + angularShortSquare q) := by
        nlinarith [mul_nonneg hC.le (mul_nonneg hnR.le (norm_nonneg t))]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 3 * ‖a‖ / 2)

theorem exists_finite_periodic_power_gap (z : ℂ) {p : ℕ} (hp : 0 < p) (hperiod : z ^ p = 1) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ n : ℕ, z ^ n ≠ 1 → delta ≤ ‖1 - z ^ n‖ := by
  let C : ℝ := 1 + ∑ k : Fin p, ‖(1 - z ^ (k : ℕ))⁻¹‖
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨1 / C, by positivity, ?_⟩
  intro n hn
  have hmod : z ^ n = z ^ (n % p) := by
    calc
      z ^ n = z ^ (n % p + p * (n / p)) := by rw [Nat.mod_add_div]
      _ = z ^ (n % p) := by rw [pow_add, pow_mul, hperiod, one_pow, mul_one]
  let k : Fin p := ⟨n % p, Nat.mod_lt n hp⟩
  have hInv : ‖(1 - z ^ n)⁻¹‖ ≤ C := by
    rw [hmod]
    have hh := Finset.single_le_sum (f := fun k : Fin p => ‖(1 - z ^ (k : ℕ))⁻¹‖)
      (fun i _ => norm_nonneg _) (Finset.mem_univ k)
    dsimp [C]
    exact hh.trans (by linarith)
  have hnorm : 0 < ‖1 - z ^ n‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hn.symm)
  have hh := mul_le_mul_of_nonneg_right hInv hnorm.le
  rw [norm_inv, inv_mul_cancel₀ hnorm.ne'] at hh
  apply (div_le_iff₀ hC).mpr
  simpa only [mul_comm] using hh

theorem exponential_small_increment {ρ : ℝ} (_hρ : 0 < ρ)
    (hcontrol : ∀ w ∈ Metric.closedBall (0 : ℂ) ρ,
      ‖dslope Complex.exp 0 w - 1‖ ≤ 1 / 2 ∧
      1 / 2 ≤ ‖dslope Complex.exp 0 w‖ ∧ dslope Complex.exp 0 w ≠ 0 ∧ ‖Complex.exp w‖ ≤ 2)
    {D : ℂ} (hD : ‖D‖ ≤ ρ) : ‖Complex.exp (-D) - 1‖ ≤ 2 * ‖D‖ := by
  have hw : -D ∈ Metric.closedBall (0 : ℂ) ρ := by simpa only [Metric.mem_closedBall, dist_zero_right, norm_neg] using hD
  have he := (hcontrol (-D) hw).1
  have htri := norm_sub_le_norm_sub_add_norm_sub (dslope Complex.exp 0 (-D)) 1 0
  simp only [sub_zero, norm_one] at htri
  have heq := sub_smul_dslope Complex.exp 0 (-D)
  simp only [sub_zero, Complex.exp_zero, smul_eq_mul] at heq
  rw [← heq, norm_mul, norm_neg]
  nlinarith [norm_nonneg D]

theorem periodic_phase_denominator_bound {φ delta ρ : ℝ} {n : ℕ} {D : ℂ}
    (hdelta : 0 < delta) (hρ : 0 < ρ)
    (hcontrol : ∀ w ∈ Metric.closedBall (0 : ℂ) ρ,
      ‖dslope Complex.exp 0 w - 1‖ ≤ 1 / 2 ∧
      1 / 2 ≤ ‖dslope Complex.exp 0 w‖ ∧ dslope Complex.exp 0 w ≠ 0 ∧ ‖Complex.exp w‖ ≤ 2)
    (hgap : delta ≤ ‖1 - Complex.exp (-((n : ℂ) * ((φ : ℂ) * Complex.I)))‖)
    (hDρ : ‖D‖ ≤ ρ) (hDδ : ‖D‖ ≤ delta / 4) :
    delta / 2 ≤ ‖1 - Complex.exp (-((n : ℂ) * ((φ : ℂ) * Complex.I) + D))‖ ∧
    ‖phaseSiteFactor ((n : ℂ) * ((φ : ℂ) * Complex.I) + D)‖ ≤ 6 / delta := by
  let z := Complex.exp (-((n : ℂ) * ((φ : ℂ) * Complex.I)))
  have hz : ‖z‖ = 1 := by simp [z, Complex.norm_exp]
  have he : Complex.exp (-((n : ℂ) * ((φ : ℂ) * Complex.I) + D)) = z * Complex.exp (-D) := by
    rw [neg_add, Complex.exp_add]
  have hdiff : ‖(1 - z * Complex.exp (-D)) - (1 - z)‖ ≤ delta / 2 := by
    have heq : (1 - z * Complex.exp (-D)) - (1 - z) = -z * (Complex.exp (-D) - 1) := by ring
    rw [heq, norm_mul, norm_neg, hz, one_mul]
    exact (exponential_small_increment hρ hcontrol hDρ).trans (by linarith)
  have hden : delta / 2 ≤ ‖1 - z * Complex.exp (-D)‖ := by
    change delta ≤ ‖1 - z‖ at hgap
    have hh := norm_sub_norm_le (1 - z) (1 - z * Complex.exp (-D))
    rw [norm_sub_rev (1 - z) (1 - z * Complex.exp (-D))] at hh
    linarith
  have hexp : ‖z * Complex.exp (-D)‖ ≤ 2 := by
    rw [norm_mul, hz, one_mul]
    exact (hcontrol (-D) (by simpa only [Metric.mem_closedBall, dist_zero_right, norm_neg] using hDρ)).2.2.2
  refine ⟨by simpa only [he] using hden, ?_⟩
  unfold phaseSiteFactor
  rw [he, norm_div]
  have hnum : ‖1 + z * Complex.exp (-D)‖ ≤ 3 := by
    have hh := norm_add_le (1 : ℂ) (z * Complex.exp (-D))
    simp only [norm_one] at hh
    linarith
  calc
    _ ≤ 3 / (delta / 2) := div_le_div₀ (by norm_num) hnum (half_pos hdelta) hden
    _ = _ := by ring

end
end IsingBulk.AnisoF002.NegativeHT
