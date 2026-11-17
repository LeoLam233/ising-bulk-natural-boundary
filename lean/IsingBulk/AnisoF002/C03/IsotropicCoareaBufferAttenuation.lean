import IsingBulk.AnisoF002.C03.IsotropicActualAttenuation

/-!
# Actual phase range and attenuation with the angular width before η
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set Metric Filter MeasureTheory

theorem exists_actual_right_phase_attenuation_buffer (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ δ K c : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < K ∧ 0 < c ∧
      ∀ η : ℝ, 0 < η → ∀ (N : ℕ), 0 < N → ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
      ∀ θ : Fin N → ℝ, (∀ i, θ i ∈ Icc (-b - δ) δ) →
        let q := (isotropicRadialParameter α ε, θ)
        (∀ i, ‖actualPhysicalPhase η τ ξ q i‖ ≤ K ∧
          c * ε ≤ -(actualPhysicalPhase η τ ξ q i).im) ∧
        ‖actualTotalPhase η τ ξ q‖ ≤ K * N ∧
          c * N * ε ≤ -(actualTotalPhase η τ ξ q).im := by
  let S := 1 + Real.cos b
  have hcosL := Real.cos_lt_cos_of_nonneg_of_le_pi hb.1.le le_rfl hb.2
  have hcosU := Real.cos_lt_cos_of_nonneg_of_le_pi (show (0 : ℝ) ≤ 0 by norm_num) hb.2.le hb.1
  rw [Real.cos_pi] at hcosL
  rw [Real.cos_zero] at hcosU
  have hS : 0 < S ∧ S < 2 := by dsimp [S]; constructor <;> linarith only [hcosL, hcosU]
  have hSb : rightBranchEndpoint S = b := by
    dsimp only [rightBranchEndpoint, S]
    rw [add_sub_cancel_left, Real.arccos_cos hb.1.le hb.2.le]
  obtain ⟨δ₀, hδ₀, hdomain⟩ := exists_actual_right_homotopy_domain S 1 hS zero_lt_one
  let δ := min 1 (δ₀ / 8)
  let K := 2 * Real.pi + 3
  let c := Real.sin α / Real.exp K
  have hδ : 0 < δ := lt_min zero_lt_one (div_pos hδ₀ (by norm_num))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδsmall : δ ≤ δ₀ / 8 := min_le_right _ _
  have hδle : δ ≤ δ₀ := by linarith only [hδsmall, hδ₀]
  have hK : 0 < K := by dsimp [K]; positivity
  have hc : 0 < c := div_pos (Real.sin_pos_of_pos_of_lt_pi hα.1 hα.2) (Real.exp_pos K)
  refine ⟨δ, K, c, hδ, hδ1, hK, hc, ?_⟩
  intro η hη N hN ε hε hεδ τ ξ hτ hξ θ hθ
  let s := isotropicRadialParameter α ε
  let q := (s, θ)
  have hrad := isotropicRadialParameter_estimates α ε hα hε (hεδ.trans hδ1)
  have hs : 0 < s.im := hrad.2.2.2.1
  have hsnear : dist s (S : ℂ) < δ₀ := by
    have hh : dist s (S : ℂ) ≤ 4 * ε := by simpa only [S, hpoint, s] using hrad.2.2.2.2
    linarith only [hh, hεδ, hδsmall, hδ₀]
  have hθD : ∀ i, θ i ∈ Icc (-rightBranchEndpoint S - δ₀) δ₀ := by
    intro i
    rw [hSb]
    exact ⟨by linarith only [(hθ i).1, hδle], (hθ i).2.trans hδle⟩
  have hdomain' := (hdomain N hN s hs hsnear η τ ξ hη ⟨hτ.1, hτ.2.trans hδle⟩ hξ θ hθD).1
  have hphase (i : Fin N) : ‖actualPhysicalPhase η τ ξ q i‖ ≤ K := by
    let w := actualHomotopyAngle η τ ξ θ i
    let v := physicalRegularCoordinate (s, w)
    have hvnear : v ∈ thickening 1 (rightCoordinateInterval S) := hdomain'.2 i
    obtain ⟨y, ⟨yr, hyr, hyrEq⟩, hdist⟩ := mem_thickening_iff.mp hvnear
    change (yr : ℂ) = y at hyrEq
    subst y
    have hyr' : |yr| ≤ b := by
      rw [abs_le]
      simpa only [hSb, mem_Icc] using hyr
    have hv : ‖v‖ ≤ Real.pi + 1 := by
      have htri := norm_le_norm_sub_add v (yr : ℂ)
      have hy : ‖(yr : ℂ)‖ ≤ b := by simpa only [Complex.norm_real, Real.norm_eq_abs] using hyr'
      rw [dist_eq_norm] at hdist
      linarith only [htri, hdist, hy, hb.2]
    have hwshift : ‖w - (θ i : ℂ)‖ ≤ τ :=
      actual_balanced_homotopy_displacement η τ ξ hτ.1 hξ θ (by simpa using hN) i
    have hθnorm : ‖(θ i : ℂ)‖ ≤ Real.pi + 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith only [(hθ i).1, (hθ i).2, hδ1, hb.2, Real.pi_pos]
    have hw : ‖w‖ ≤ Real.pi + 2 := by
      have htri := norm_le_norm_sub_add w (θ i : ℂ)
      linarith only [htri, hwshift, hθnorm, hτ.2, hδ1]
    have he : actualPhysicalPhase η τ ξ q i = v - w := by
      dsimp only [q, actualPhysicalPhase, v, physicalRegularCoordinate, w]
      ring
    rw [he]
    exact (norm_sub_le v w).trans (by dsimp [K]; linarith only [hv, hw])
  have hatten (i : Fin N) : c * ε ≤ -(actualPhysicalPhase η τ ξ q i).im := by
    have him := actual_balanced_homotopy_im_lower s η τ ξ hη hτ.1 hξ.1 θ i
    have hW : 0 < (isotropicDispersion (s, actualHomotopyAngle η τ ξ θ i)).im := hs.trans_le him
    have hh := upperPhysicalPhase_attenuation_lower _ hW K (hphase i)
    have hl : Real.sin α * ε ≤ (isotropicDispersion (s, actualHomotopyAngle η τ ξ θ i)).im :=
      hrad.1.trans him
    apply le_trans _ hh
    change (Real.sin α / Real.exp K) * ε ≤ _
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right hl (Real.exp_pos K).le
  refine ⟨fun i => ⟨hphase i, hatten i⟩, ?_, ?_⟩
  · apply (norm_sum_le Finset.univ (fun i => actualPhysicalPhase η τ ξ q i)).trans
    have hh := Finset.sum_le_sum (fun (i : Fin N) (_ : i ∈ Finset.univ) => hphase i)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm] using hh
  · have hh := Finset.sum_le_sum (fun (i : Fin N) (_ : i ∈ Finset.univ) => hatten i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Finset.sum_neg_distrib] at hh
    have he : (actualTotalPhase η τ ξ q).im = ∑ i, (actualPhysicalPhase η τ ξ q i).im := by
      simp only [actualTotalPhase, Complex.im_sum]
    rw [he]
    nlinarith only [hh]

end IsingBulk.AnisoF002.Isotropic
