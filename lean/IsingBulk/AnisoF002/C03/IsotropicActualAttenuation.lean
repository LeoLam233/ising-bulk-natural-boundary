import IsingBulk.AnisoF002.C03.IsotropicRadialApproach
import IsingBulk.AnisoF002.C03.IsotropicPhaseTransport
import IsingBulk.AnisoF002.C03.IsotropicFrozenProjection

/-!
# Actual physical attenuation and phase range on the complete right rectangle

The common image neighborhood bounds the actual physical phase, including
the negative branch sliver. The full balanced displacement increases the
imaginary dispersion. The exact cosine equation then gives a positive
attenuation per particle, with all constants fixed before particle number.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric

theorem sinh_le_exp_mul_on_interval (K a : ℝ) (ha : a ∈ Icc 0 K) :
    Real.sinh a ≤ Real.exp K * a := by
  have hbound (x : ℝ) (hx : x ∈ Icc 0 K) : ‖deriv Real.sinh x‖ ≤ Real.exp K := by
    rw [Real.deriv_sinh, Real.norm_eq_abs, abs_of_pos (Real.cosh_pos x)]
    have hh := Real.cosh_add_sinh x
    have hs := Real.sinh_nonneg_iff.mpr hx.1
    exact (show Real.cosh x ≤ Real.exp x by linarith only [hh, hs]).trans
      (Real.exp_le_exp.mpr hx.2)
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := Icc 0 K) (f := Real.sinh) (fun x _ => Real.differentiable_sinh x) hbound
    (convex_Icc 0 K) (left_mem_Icc.mpr (ha.1.trans ha.2)) ha
  simpa only [Real.sinh_zero, sub_zero, Real.norm_eq_abs,
    abs_of_nonneg (Real.sinh_nonneg_iff.mpr ha.1), abs_of_nonneg ha.1] using hh

theorem actual_balanced_homotopy_im_lower {ι : Type*} [Fintype ι]
    (s : ℂ) (η τ ξ : ℝ) (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ)
    (θ : ι → ℝ) (i : ι) :
    s.im ≤ (isotropicDispersion (s, actualHomotopyAngle η τ ξ θ i)).im := by
  have hsign := balancedShift_sine_nonpos (ξ * (τ / Fintype.card ι)) θ
    (fun j => upperPeriodicBump η (θ j)) (fun j => lowerPeriodicBump η (θ j))
    (by positivity) (fun j => (upperPeriodicBump_bounds η (θ j)).1)
    (fun j => (lowerPeriodicBump_bounds η (θ j)).1)
    (fun j => (actual_bump_sine_signs hη (θ j)).1)
    (fun j => (actual_bump_sine_signs hη (θ j)).2) i
  have hh := sinh_mul_nonpos_of_mul_nonpos hsign
  rw [actualHomotopyAngle, balancedHomotopyCoordinate, contourCoordinate,
    isotropicDispersion_contour_im]
  linarith only [hh]

theorem upperPhysicalPhase_attenuation_lower (W : ℂ) (hW : 0 < W.im)
    (K : ℝ) (hK : ‖upperPhysicalPhase W‖ ≤ K) :
    W.im / Real.exp K ≤ -(upperPhysicalPhase W).im := by
  let φ := upperPhysicalPhase W
  have ha : 0 < -φ.im := neg_pos.mpr (upperPhysicalPhase_im_neg W hW)
  have haK : -φ.im ≤ K :=
    (neg_le_abs φ.im).trans ((Complex.abs_im_le_norm φ).trans hK)
  have hsinh := sinh_le_exp_mul_on_interval K (-φ.im) ⟨ha.le, haK⟩
  have hcos : W.im = Real.sin φ.re * Real.sinh (-φ.im) := by
    rw [← upperPhysicalPhase_cos W, Complex.cos_eq]
    simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cosh,
      ← Complex.ofReal_sinh, Complex.sub_im, Complex.mul_im, Complex.mul_re,
      Complex.ofReal_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
      zero_mul, mul_zero, sub_zero, add_zero, mul_one, zero_sub, Real.sinh_neg, φ]
    ring
  have hsin := mul_le_mul_of_nonneg_right (Real.sin_le_one φ.re)
    (Real.sinh_nonneg_iff.mpr ha.le)
  apply (div_le_iff₀ (Real.exp_pos K)).mpr
  nlinarith only [hcos, hsin, hsinh]

/-- The entire actual right image, with both endpoint slivers, has a
bounded individual phase and linear total attenuation. No population
fraction is assumed positive. -/
theorem exists_actual_right_phase_attenuation (α b η : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) (hη : 0 < η) :
    ∃ δ K c : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < K ∧ 0 < c ∧
      ∀ (N : ℕ), 0 < N → ∀ ε : ℝ, 0 < ε → ε ≤ δ →
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
  intro N hN ε hε hεδ τ ξ hτ hξ θ hθ
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
