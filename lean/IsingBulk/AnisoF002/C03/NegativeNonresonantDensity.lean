import IsingBulk.AnisoF002.C03.NegativeNonresonantPhase
import IsingBulk.AnisoF002.C03.NegativeOuterCycleControl

/-!
# Complete nonresonant density bounds on c/N disks

The inner periodic phase gap and the outer positive-real-part estimate
cover every original real angular tuple.  Their constants are chosen
before N; no winding or particle class is omitted.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology

set_option maxHeartbeats 1000000 in
theorem exists_actual_nonresonant_inner_site_control {B : ℂ → ℂ} {φ : ℝ} {p : ℕ}
    (hB : AnalyticAt ℂ B 0) (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0)
    (hp : 0 < p) (hperiod : Complex.exp (-((p : ℂ) * ((φ : ℂ) * Complex.I))) = 1) :
    ∃ s r K : ℝ, 0 < s ∧ 0 < r ∧ 0 < K ∧ ∀ n : ℕ, 0 < n →
      Complex.exp (-((n : ℂ) * ((φ : ℂ) * Complex.I))) ≠ 1 →
      ∀ q : Fin n → ℝ, angularShortSquare q ≤ s →
      ∀ t ∈ Metric.closedBall (0 : ℂ) (r / (n : ℝ)),
        AnalyticAt ℂ (fun u => phaseSiteFactor (realPhaseTotal B φ n q u)) t ∧
        ‖phaseSiteFactor (realPhaseTotal B φ n q t)‖ ≤ K := by
  let z := Complex.exp (-((φ : ℂ) * Complex.I))
  have hz (n : ℕ) : Complex.exp (-((n : ℂ) * ((φ : ℂ) * Complex.I))) = z ^ n := by
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  obtain ⟨delta, hd, hgap⟩ := exists_finite_periodic_power_gap z hp (by rw [← hz]; exact hperiod)
  obtain ⟨ρ, hρ, hρc⟩ := exists_exponential_dslope_control
  obtain ⟨R, s₀, C, hR, hs₀, hC, hinc⟩ := exists_actual_inner_phase_increment hB hφ hπ hBi
  obtain ⟨d⟩ := (exists_negative_global_controls hB hφ hπ hBi).2
  let eps : ℝ := min ρ (delta / 4)
  let s : ℝ := min s₀ (eps / (2 * C))
  let r : ℝ := min R (min d.radius (eps / (2 * C)))
  have heps : 0 < eps := lt_min hρ (by positivity)
  have hs : 0 < s := lt_min hs₀ (by positivity)
  have hr : 0 < r := lt_min hR (lt_min d.radius_pos (by positivity))
  refine ⟨s, r, 6 / delta, hs, hr, by positivity, ?_⟩
  intro n hn hne q hq t ht
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have htR : t ∈ Metric.closedBall (0 : ℂ) R := Metric.closedBall_subset_closedBall
    ((div_le_self hr.le hn1).trans (min_le_left _ _)) ht
  have htd : t ∈ Metric.closedBall (0 : ℂ) d.radius := Metric.closedBall_subset_closedBall
    ((div_le_self hr.le hn1).trans ((min_le_right _ _).trans (min_le_left _ _))) ht
  have htNorm : (n : ℝ) * ‖t‖ ≤ r := by
    have hh : ‖t‖ ≤ r / (n : ℝ) := by simpa only [Metric.mem_closedBall, dist_zero_right] using ht
    exact (mul_comm (n : ℝ) ‖t‖ ▸ ((le_div_iff₀ hnR).mp hh))
  let D : ℂ := realPhaseTotal B φ n q t - (n : ℂ) * ((φ : ℂ) * Complex.I)
  have hD : ‖D‖ ≤ eps := by
    have hh := hinc n hn q (hq.trans (min_le_left _ _)) t htR
    have hsC : C * angularShortSquare q ≤ eps / 2 := by
      have h := (le_div_iff₀ (by positivity : 0 < 2 * C)).mp
        (hq.trans (min_le_right _ _) : angularShortSquare q ≤ eps / (2 * C))
      nlinarith
    have hrC : C * r ≤ eps / 2 := by
      have h := (le_div_iff₀ (by positivity : 0 < 2 * C)).mp
        ((min_le_right _ _).trans (min_le_right _ _) : r ≤ eps / (2 * C))
      nlinarith
    have hNt := mul_le_mul_of_nonneg_left htNorm hC.le
    exact hh.trans (by nlinarith)
  have hgapn : delta ≤ ‖1 - Complex.exp (-((n : ℂ) * ((φ : ℂ) * Complex.I)))‖ := by
    rw [hz]
    exact hgap n (by rwa [← hz])
  have hden := periodic_phase_denominator_bound hd hρ hρc hgapn
    (hD.trans (min_le_left _ _)) (hD.trans (min_le_right _ _))
  have hphaseEq : (n : ℂ) * ((φ : ℂ) * Complex.I) + D = realPhaseTotal B φ n q t := by dsimp [D]; ring
  rw [hphaseEq] at hden
  have hG : AnalyticAt ℂ (realPhaseTotal B φ n q) t := by
    have heq : realPhaseTotal B φ n q = fun u =>
        edgeTotalPhase (negativeGlobalCenter B φ) (negativeGlobalCoefficient B) u q := by
      funext u
      exact realPhaseTotal_eq_edge B φ n q u
    rw [heq]
    exact d.totalPhase_parameter_analytic q htd
  have hden0 : 1 - Complex.exp (-realPhaseTotal B φ n q t) ≠ 0 :=
    norm_pos_iff.mp ((half_pos hd).trans_le hden.1)
  refine ⟨?_, hden.2⟩
  have he := hG.neg.cexp
  exact (analyticAt_const.add he).div (analyticAt_const.sub he) hden0

theorem exists_actual_nonresonant_density_control {b B : ℂ → ℂ} {φ : ℝ} {p : ℕ}
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0)
    (hbsq : ∀ t, b t ^ 2 = B t)
    (hp : 0 < p) (hperiod : Complex.exp (-((p : ℂ) * ((φ : ℂ) * Complex.I))) = 1) :
    ∃ r M kappa : ℝ, 0 < r ∧ 0 < M ∧ 0 < kappa ∧ ∀ n : ℕ, 0 < n →
      Complex.exp (-((n : ℂ) * ((φ : ℂ) * Complex.I))) ≠ 1 →
      ∀ q : Fin n → ℝ, ∀ t ∈ Metric.closedBall (0 : ℂ) (r / (n : ℝ)),
        AnalyticAt ℂ (fun u => realNegativeDensity b B φ n u q) t ∧
        ‖realNegativeDensity b B φ n t q‖ ≤
          M * Real.exp (-kappa * (n : ℝ) ^ 2) / ‖windingNormalization n‖ := by
  obtain ⟨s, ri, K, hs, hri, hK, hsite⟩ := exists_actual_nonresonant_inner_site_control hB hφ hπ hBi hp hperiod
  obtain ⟨ro, Mo, ko, hro, hMo, hko, hout⟩ := exists_actual_outer_density_control hb hB hφ hπ hBi hbsq hs
  obtain ⟨rh, Mh, kh, hrh, hMh, hkh, hnum⟩ := exists_actual_numerator_gaussian_control hb hB hφ hπ hBi hbsq
  let r := min ri (min ro rh)
  let kappa := min ko kh
  let M := Mo + Mh * K
  have hr : 0 < r := lt_min hri (lt_min hro hrh)
  have hk : 0 < kappa := lt_min hko hkh
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨r, M, kappa, hr, hM, hk, ?_⟩
  intro n hn hne q t ht
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have htri : t ∈ Metric.closedBall (0 : ℂ) (ri / (n : ℝ)) :=
    Metric.closedBall_subset_closedBall (div_le_div_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg n)) ht
  have htro : t ∈ Metric.closedBall (0 : ℂ) (ro / (n : ℝ)) :=
    Metric.closedBall_subset_closedBall (div_le_div_of_nonneg_right
      ((min_le_right _ _).trans (min_le_left _ _)) (Nat.cast_nonneg n)) ht
  have htrh : t ∈ Metric.closedBall (0 : ℂ) rh := Metric.closedBall_subset_closedBall
    ((div_le_self hr.le hn1).trans ((min_le_right _ _).trans (min_le_right _ _))) ht
  have heo : Real.exp (-ko * (n : ℝ) ^ 2) ≤ Real.exp (-kappa * (n : ℝ) ^ 2) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (neg_le_neg (min_le_left _ _)) (sq_nonneg _)
  have heh : Real.exp (-kh * (n : ℝ) ^ 2) ≤ Real.exp (-kappa * (n : ℝ) ^ 2) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (neg_le_neg (min_le_right _ _)) (sq_nonneg _)
  by_cases hq : angularShortSquare q ≤ s
  · obtain ⟨hHa, hHb⟩ := hnum n q t htrh
    obtain ⟨hSa, hSb⟩ := hsite n hn hne q hq t htri
    refine ⟨hHa.mul hSa, ?_⟩
    unfold realNegativeDensity
    rw [norm_mul]
    calc
      _ ≤ (Mh * Real.exp (-kh * (n : ℝ) ^ 2) / ‖windingNormalization n‖) * K :=
        mul_le_mul hHb hSb (norm_nonneg _) (by positivity)
      _ ≤ (Mh * Real.exp (-kappa * (n : ℝ) ^ 2) / ‖windingNormalization n‖) * K := by gcongr
      _ = (Mh * K) * Real.exp (-kappa * (n : ℝ) ^ 2) / ‖windingNormalization n‖ := by ring
      _ ≤ _ := by gcongr; dsimp [M]; linarith
  · obtain ⟨ha, hbnd⟩ := hout n hn q (le_of_not_ge hq) t htro
    refine ⟨ha, hbnd.trans ?_⟩
    apply div_le_div_of_nonneg_right _ (norm_nonneg _)
    exact mul_le_mul (by dsimp [M]; nlinarith [mul_pos hMh hK]) heo (Real.exp_nonneg _) hM.le

end
end IsingBulk.AnisoF002.NegativeHT
