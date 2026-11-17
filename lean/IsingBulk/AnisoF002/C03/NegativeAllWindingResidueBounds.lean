import IsingBulk.AnisoF002.C03.NegativeCyclePoleUniqueness
import IsingBulk.AnisoF002.C03.NegativeAllWindingPoleBound
import IsingBulk.AnisoF002.C03.RegularWindingNumeratorBound

/-!
# Uniform complete residue bounds for every actual inner winding

The full physical phase derivative is bounded below by a constant times
N.  The exact near-one-half pole location and the complete normalized
Vandermonde numerator are combined before choosing any particle number
or Taylor order.  The angular cutoff remains freely shrinkable.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter
open scoped Topology BigOperators

theorem angularShortSquare_eq_of_sq_sum_le_pi_sq {n : ℕ} (v : Fin n → ℝ)
    (hv : (∑ i, v i ^ 2) ≤ Real.pi ^ 2) : angularShortSquare v = ∑ i, v i ^ 2 := by
  apply Finset.sum_congr rfl
  intro i _
  have hi : v i ^ 2 ≤ ∑ j, v j ^ 2 := Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
  have habs : |v i| ≤ Real.pi := by nlinarith [sq_abs (v i), abs_nonneg (v i), Real.pi_pos]
  have he : unsignedShortAngle (v i) = |v i| := by
    unfold unsignedShortAngle
    rw [← Real.cos_abs (v i)]
    exact Real.arccos_cos (abs_nonneg _) habs
  rw [he, sq_abs]

theorem exists_actual_phase_derivative_lower {B : ℂ → ℂ} {φ : ℝ}
    (hB : AnalyticAt ℂ B 0) (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0) :
    ∃ R s A : ℝ, 0 < R ∧ 0 < s ∧ 0 < A ∧
      ∀ n : ℕ, 0 < n → ∀ q : Fin n → ℝ, angularShortSquare q ≤ s →
      ∀ T : ℂ, ‖T‖ ≤ R →
        realPhaseTotal B φ n q T = (n : ℂ) * ((φ : ℂ) * Complex.I) →
        A * (n : ℝ) ≤ ‖deriv (realPhaseTotal B φ n q) T‖ := by
  obtain ⟨R, s, C, a, hR, hs, _, _, ha, hd⟩ := exists_actual_inner_pole_data hB hφ hπ hBi
  refine ⟨R, s, ‖a‖ / 2, hR, hs, half_pos (norm_pos_iff.mpr ha), ?_⟩
  intro n hn q hq T hT hphase
  obtain ⟨d⟩ := hd n hn
  have he : T = d.pole q := d.phase_zero_unique hn q hq hT hphase
  have hmem : T ∈ Metric.closedBall (0 : ℂ) R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hT
  have hF := (d.average_analytic q hq T hmem).differentiableAt
  rw [realPhaseTotal_deriv B φ hn q T hF, norm_mul, norm_natCast]
  have hlo := (d.factor_bounds q hq T hmem).1
  rw [← he, dslope_same] at hlo
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg n)

set_option maxHeartbeats 1000000 in
theorem exists_actual_all_winding_residue_bounds {b B : ℂ → ℂ} {φ : ℝ}
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0)
    (hbsq : ∀ t, b t ^ 2 = B t) :
    ∃ R s A K C : ℝ, 0 < R ∧ 0 < s ∧ 0 < A ∧ 0 < K ∧ 0 < C ∧ K * s ≤ 1 / 4 ∧
      ∀ σ : ℝ, 0 < σ → σ ≤ s → ∀ n : ℕ, 0 < n → ∀ v : Fin n → ℝ, ∀ T : ℂ,
      (∑ i, v i ^ 2) ≤ σ → ‖T‖ ≤ R →
      realPhaseTotal B φ n v T = (n : ℂ) * ((φ : ℂ) * Complex.I) →
        ‖T - (((∑ i, v i ^ 2) / (2 * (n : ℝ)) : ℝ) : ℂ)‖ ≤
          K * (∑ i, v i ^ 2) ^ 2 / (n : ℝ) ∧
        ((1 / 2 - K * σ) * (∑ i, v i ^ 2)) / (n : ℝ) ≤ ‖T‖ ∧
        A * (n : ℝ) ≤ ‖deriv (realPhaseTotal B φ n v) T‖ ∧
        ‖completeNegativeNumerator n b (negativeGlobalPhase B φ) 0 T (fun i => (v i : ℂ))‖ ≤
          allWindingCenterMagnitude n (b 0) φ * realWindingVandermondeSquared n v * Real.exp (C * (n : ℝ) * σ) ∧
        ∀ k : ℕ, 0 < (∑ i, v i ^ 2) →
          ‖(-(2 * completeNegativeNumerator n b (negativeGlobalPhase B φ) 0 T (fun i => (v i : ℂ))) /
              deriv (realPhaseTotal B φ n v) T) / T ^ k‖ ≤
            (2 * allWindingCenterMagnitude n (b 0) φ * realWindingVandermondeSquared n v *
              Real.exp (C * (n : ℝ) * σ)) /
            (A * (n : ℝ)) / (((1 / 2 - K * σ) * (∑ i, v i ^ 2)) / (n : ℝ)) ^ k := by
  obtain ⟨Rd, sd, A, hRd, hsd, hA, hder⟩ := exists_actual_phase_derivative_lower hB hφ hπ hBi
  obtain ⟨e, K, he, hK, hpole⟩ := exists_actual_all_winding_pole_quadratic_bound hB hφ hπ hBi
  obtain ⟨sh, C, hsh, hC, hnum⟩ := exists_actual_all_winding_numerator_bound_explicit hb hB hφ hπ hBi hbsq
  let R := min Rd e
  let s := min sd (min e (min sh (min (Real.pi ^ 2) (1 / (4 * K)))))
  have hR : 0 < R := lt_min hRd he
  have hs : 0 < s := lt_min hsd (lt_min he (lt_min hsh (lt_min (sq_pos_of_pos Real.pi_pos) (by positivity))))
  have hsd' : s ≤ sd := min_le_left _ _
  have hse : s ≤ e := (min_le_right _ _).trans (min_le_left _ _)
  have hsh' : s ≤ sh := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsπ : s ≤ Real.pi ^ 2 := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hsK : K * s ≤ 1 / 4 := by
    have hh : s ≤ 1 / (4 * K) := (min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    have h := (le_div_iff₀ (mul_pos (by norm_num) hK)).mp hh
    nlinarith
  refine ⟨R, s, A, K, C, hR, hs, hA, hK, hC, hsK, ?_⟩
  intro σ hσ hσs n hn v T hS hT hphase
  let S : ℝ := ∑ i, v i ^ 2
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg (v i))
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hKS : K * σ ≤ 1 / 4 := (mul_le_mul_of_nonneg_left hσs hK.le).trans hsK
  have halpha : 0 < 1 / 2 - K * σ := by linarith
  obtain ⟨herr, hlow⟩ := hpole n hn v T (hS.trans (hσs.trans hse))
    (hT.trans (min_le_right _ _)) hphase
  have hcenter : ‖(((S / (2 * (n : ℝ)) : ℝ) : ℂ))‖ = S / (2 * (n : ℝ)) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hTU : ‖T‖ ≤ S / (n : ℝ) := by
    have htri := norm_le_norm_sub_add T (((S / (2 * (n : ℝ)) : ℝ) : ℂ))
    rw [hcenter] at htri
    have hKS' : K * S ≤ 1 / 4 := (mul_le_mul_of_nonneg_left hS hK.le).trans hKS
    have herror : K * S ^ 2 / (n : ℝ) ≤ S / (2 * (n : ℝ)) := by
      apply (div_le_iff₀ hN).mpr
      have heq : S / (2 * (n : ℝ)) * (n : ℝ) = S / 2 := by field_simp
      rw [heq]
      nlinarith
    change ‖T - (((S / (2 * (n : ℝ)) : ℝ) : ℂ))‖ ≤ K * S ^ 2 / (n : ℝ) at herr
    have heq : S / (2 * (n : ℝ)) + S / (2 * (n : ℝ)) = S / (n : ℝ) := by ring
    linarith
  have hlower : ((1 / 2 - K * σ) * S) / (n : ℝ) ≤ ‖T‖ := by
    apply le_trans _ hlow
    apply div_le_div_of_nonneg_right _ hN.le
    have hh := mul_le_mul_of_nonneg_left hS hK.le
    nlinarith
  have hshort : angularShortSquare v = S := angularShortSquare_eq_of_sq_sum_le_pi_sq v
    (hS.trans (hσs.trans hsπ))
  have hderiv : A * (n : ℝ) ≤ ‖deriv (realPhaseTotal B φ n v) T‖ :=
    hder n hn v (by rw [hshort]; exact hS.trans (hσs.trans hsd')) T
      (hT.trans (min_le_left _ _)) hphase
  have hnum' := hnum n hn v T (hS.trans (hσs.trans hsh')) hTU
  have hH0 : 0 ≤ allWindingCenterMagnitude n (b 0) φ := by
    unfold allWindingCenterMagnitude
    exact div_nonneg (pow_nonneg (norm_nonneg _) _)
      (mul_nonneg (by positivity) (pow_nonneg (Real.sin_pos_of_pos_of_lt_pi hφ hπ).le _))
  have hV0 := realWindingVandermondeSquared_nonneg n v
  have hnumBound : ‖completeNegativeNumerator n b (negativeGlobalPhase B φ) 0 T (fun i => (v i : ℂ))‖ ≤
      allWindingCenterMagnitude n (b 0) φ * realWindingVandermondeSquared n v * Real.exp (C * (n : ℝ) * σ) := by
    apply hnum'.trans
    gcongr
  refine ⟨herr, hlower, hderiv, hnumBound, ?_⟩
  intro k hSp
  have hden : 0 < ((1 / 2 - K * σ) * S) / (n : ℝ) := by positivity
  rw [norm_div, norm_div, norm_neg, norm_mul, Complex.norm_ofNat, norm_pow]
  simpa only [mul_assoc] using div_le_div₀ (by positivity)
    (div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hnumBound (by norm_num : (0 : ℝ) ≤ 2))
      (mul_pos hA hN) hderiv)
    (pow_pos hden k) (pow_le_pow_left₀ hden.le hlower k)

end
end IsingBulk.AnisoF002.NegativeHT
