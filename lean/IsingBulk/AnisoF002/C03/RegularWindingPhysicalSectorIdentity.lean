import IsingBulk.AnisoF002.C03.RegularWindingPhysicalSectors

/-!
# Exact original inner Taylor coefficient as the sum of all physical windings

The boundedness used for the finite measure decomposition is proved from
the complete physical-cycle phase gap and the actual pole subtraction.
No sectorwise summability or integrability assumption is imposed.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter MeasureTheory IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology BigOperators

theorem actualInnerPoleDensity_bounded {b B : ℂ → ℂ} {φ r s M kappa : ℝ} {n : ℕ}
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0)
    (hbsq : ∀ t, b t ^ 2 = B t)
    (d : InnerRemainderFamily b B φ (n + 1) r s M kappa)
    (hr : 0 < r) (hs : 0 ≤ s) (hM : 0 ≤ M) (hn : Odd (n + 1))
    (hres : Complex.exp (-(((n + 1 : ℕ) : ℂ) * ((φ : ℂ) * Complex.I))) = 1) (j : ℕ) :
    ∃ E : ℝ, 0 < E ∧ ∀ q : Fin n → ℝ,
      ‖actualInnerPoleDensity d j (negativeConstrainedAngles q)‖ ≤ E := by
  obtain ⟨c, Mp, kp, A, hc, hMp, _, hA, hphys⟩ :=
    exists_actual_physical_cycle_control hb hB hφ hπ hBi hbsq
  obtain ⟨rD, hrD, hm⟩ := exists_actual_real_density_measurable hb hB hφ hπ hBi hbsq
  let cN : ℝ := c / ((n + 1 : ℕ) : ℝ) ^ 2
  let EN : ℝ := Mp * ((n + 1 : ℕ) : ℝ) * Real.exp (-kp * ((n + 1 : ℕ) : ℝ) ^ 2) /
    ‖windingNormalization (n + 1)‖
  have hcN : 0 < cN := by dsimp [cN]; positivity
  have hEN : 0 ≤ EN := by dsimp [EN]; positivity
  have hzero : (0 : ℂ) ∈ Metric.closedBall 0 cN := Metric.mem_closedBall_self hcN.le
  have hbound (q : Fin n → ℝ) :
      ‖realNegativeDensity b B φ (n + 1) 0 (negativeConstrainedAngles q)‖ ≤ EN :=
    (hphys n hn q 0 hzero).2.2
  have hsep (q : Fin n → ℝ) (hq : angularShortSquare (negativeConstrainedAngles q) ≤ s) :
      cN ≤ ‖d.pole (negativeConstrainedAngles q)‖ :=
    (extracted_pole_outside_physical_disk d hc hA q hq
      (fun t ht => (hphys n hn q t ht).2.1)).le
  obtain ⟨A0, P0, L, hL, _, _, hAb, hPb, hsame, hzeroA⟩ :=
    exists_inner_cycle_pole_representatives d hr hs hM hcN hEN hres
      (hm (n + 1) (Nat.succ_pos n) 0 (Metric.mem_ball_self hrD)) hbound hsep
  refine ⟨L / cN ^ (j + 1), div_pos hL (pow_pos hcN _), ?_⟩
  intro q
  have he : actualInnerPoleDensity d j (negativeConstrainedAngles q) = A0 q / P0 q ^ (j + 1) := by
    by_cases hq : angularShortSquare (negativeConstrainedAngles q) ≤ s
    · simp only [actualInnerPoleDensity, shortCutDensity, hq, ↓reduceIte,
        (hsame q hq).1, (hsame q hq).2]
    · simp only [actualInnerPoleDensity, shortCutDensity, hq, ↓reduceIte, hzeroA q hq, zero_div]
  rw [he, norm_div, norm_pow]
  exact div_le_div₀ hL.le (hAb q) (pow_pos hcN _) (pow_le_pow_left₀ hcN.le (hPb q) _)

theorem innerCyclePoleCoefficient_all_winding_identity {b B : ℂ → ℂ}
    {φ r s M kappa R s0 : ℝ} {n : ℕ}
    (d : InnerRemainderFamily b B φ (n + 1) r s M kappa)
    (hu : ActualPhaseUniqueOn B φ R s0) (hR : r / (4 * (n + 1 : ℕ)) ≤ R)
    (hs0 : s ≤ s0) (hsπ : s < Real.pi ^ 2) (hn : Odd (n + 1)) (j : ℕ)
    (hm : Measurable (actualInnerPoleDensity d j))
    (hbnd : ∃ E : ℝ, 0 < E ∧ ∀ q : Fin n → ℝ,
      ‖actualInnerPoleDensity d j (negativeConstrainedAngles q)‖ ≤ E) :
    innerCyclePoleCoefficient d j =
      ∑ w ∈ windingSectorIndices n, physicalWindingSectorCoefficient d j w := by
  obtain ⟨E, hE, hbound⟩ := hbnd
  let F : (Fin (n + 1) → ℝ) → ℂ := fun q => d.actualResidue q / d.pole q ^ (j + 1)
  have hp : AllAnglePeriodic (shortCutDensity s F) :=
    actualInnerPoleDensity_periodic d (Nat.succ_pos n) hu hR hs0 j
  have hid := windingSector_integral_complete F hp hn hsπ hm hE.le hbound
  rw [innerCyclePoleCoefficient_eq_density]
  change -(∫ q in regularAngularBox n, shortCutDensity s F (negativeConstrainedAngles q)) = _
  rw [hid, ← Finset.sum_neg_distrib]
  rfl

theorem exists_actual_winding_sector_identity_radii {b B : ℂ → ℂ} {φ : ℝ}
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0)
    (hbsq : ∀ t, b t ^ 2 = B t) :
    ∃ R s0 : ℝ, 0 < R ∧ 0 < s0 ∧ ∀ n : ℕ, Odd (n + 1) →
      ∀ r s M kappa : ℝ, ∀ d : InnerRemainderFamily b B φ (n + 1) r s M kappa,
      0 < r → 0 ≤ s → 0 ≤ M → s ≤ s0 → r / (4 * (n + 1 : ℕ)) ≤ R →
      Complex.exp (-(((n + 1 : ℕ) : ℂ) * ((φ : ℂ) * Complex.I))) = 1 →
      ∀ j : ℕ, innerCyclePoleCoefficient d j =
        ∑ w ∈ windingSectorIndices n, physicalWindingSectorCoefficient d j w := by
  obtain ⟨Ru, su, hRu, hsu, hu⟩ := exists_actual_phase_unique_ball hB hφ hπ hBi
  obtain ⟨rJ, hrJ, hJ⟩ := exists_actual_inner_pole_density_measurable_radius hb hB hφ hπ hBi hbsq
  let R := min Ru (rJ / 2)
  let s0 := min su (Real.pi ^ 2 / 2)
  have hR : 0 < R := lt_min hRu (half_pos hrJ)
  have hs0 : 0 < s0 := lt_min hsu (by positivity)
  refine ⟨R, s0, hR, hs0, ?_⟩
  intro n hn r s M kappa d hr hs hM hss0 hrR hres j
  have hrsu : r / (4 * (n + 1 : ℕ)) ≤ Ru := hrR.trans (min_le_left _ _)
  have hssu : s ≤ su := hss0.trans (min_le_left _ _)
  have hsπ : s < Real.pi ^ 2 := (hss0.trans (min_le_right _ _)).trans_lt (by nlinarith [Real.pi_pos])
  have hrJ' : r / (4 * (n + 1 : ℕ)) < rJ :=
    (hrR.trans (min_le_right _ _)).trans_lt (by linarith)
  exact innerCyclePoleCoefficient_all_winding_identity d hu hrsu hssu hsπ hn j
    (hJ (n + 1) (Nat.succ_pos n) r s M kappa d hs hrJ' j)
    (actualInnerPoleDensity_bounded hb hB hφ hπ hBi hbsq d hr hs hM hn hres j)

end
end IsingBulk.AnisoF002.NegativeHT
