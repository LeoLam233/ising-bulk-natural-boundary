import IsingBulk.AnisoF002.C03.IsotropicCoareaBufferRatio
import IsingBulk.AnisoF002.C03.IsotropicCoareaBufferAttenuation
import IsingBulk.AnisoF002.C03.IsotropicActualPositiveCoarea

/-!
# The complete actual positive fiber integral with geometry chosen before η
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set Metric MeasureTheory

theorem exists_actual_positive_extreme_integral_buffer (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b →
      ∃ δ C : ℝ, 0 < δ ∧ δ ≤ β ∧ 0 < C ∧
      ∀ (N : ℕ), 0 < N → ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
      ∀ (θ : Fin N → ℝ) (i j : Fin N) (r γ A B : ℝ), 0 < r → A ≤ B →
        Icc A B ⊆ positiveExtremeFiber θ i j b β r →
        (∫ t in A..B, actualExtremeFiberDensity (isotropicRadialParameter α ε) η τ ξ γ θ i j t) ≤
          C * N * Real.sqrt (|angularMean (fun k => θ k + b)| + r + ε) / r *
            (1 + |Real.log ε|) := by
  obtain ⟨βR, hβR, hβR1, hratioData⟩ :=
    exists_actual_constrained_extreme_ratio_buffer α b hα hb hpoint
  obtain ⟨βA, K, c, hβA, _, hK, hc, hattenData⟩ :=
    exists_actual_right_phase_attenuation_buffer α b hα hb hpoint
  obtain ⟨C₀, hC₀, hcoarea⟩ := exists_oblique_phase_fiber_integral_bound
  let β := min βR βA
  have hβ : 0 < β := lt_min hβR hβA
  have hβR' : β ≤ βR := min_le_left _ _
  have hβA' : β ≤ βA := min_le_right _ _
  have hβ1 : β ≤ 1 := hβR'.trans hβR1
  refine ⟨β, hβ, hβ1, ?_⟩
  intro η hη hwidth
  obtain ⟨δR, R, hδR, _, hR, hratio⟩ := hratioData η hη hwidth
  have hatten := hattenData η hη
  let δ := min δR β
  let C := C₀ * R * Real.sqrt 2 * (1 + 2 * K) * (1 + |Real.log c|)
  have hδ : 0 < δ := lt_min hδR hβ
  have hδR' : δ ≤ δR := min_le_left _ _
  have hδβ : δ ≤ β := min_le_right _ _
  have hδA' : δ ≤ βA := hδβ.trans hβA'
  have hδ1 : δ ≤ 1 := hδβ.trans hβ1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨δ, C, hδ, hδβ, hC, ?_⟩
  intro N hN ε hε hεδ τ ξ hτ hξ θ i j r γ A B hr hAB hfiber
  let s := isotropicRadialParameter α ε
  let μ := angularMean (fun k => θ k + b)
  let T := |μ| + r + ε
  let G₀ : ℝ → ℂ := fun t => actualTotalPhase η τ ξ (s, constrainedAngleLine θ i j t)
  let G : ℝ → ℂ := fun t => G₀ t - (γ : ℂ)
  let D : ℝ → ℝ := fun t => (frozenObliqueRotation *
    (actualFullPhaseDerivative s η τ ξ (constrainedAngleLine θ i j t) i -
      actualFullPhaseDerivative s η τ ξ (constrainedAngleLine θ i j t) j)).re
  let F : ℝ → ℝ := fun t =>
    ‖(1 + actualPhaseSlope s η τ ξ (constrainedAngleLine θ i j t) i) *
      (1 + actualPhaseSlope s η τ ξ (constrainedAngleLine θ i j t) j)‖
  let a₀ := min 1 (c * N * ε)
  let Q := R * Real.sqrt 2 * Real.sqrt T / r
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hnpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hT : 0 < T := by dsimp [T]; positivity
  have ha₀ : 0 < a₀ := lt_min zero_lt_one (mul_pos (mul_pos hc hnpos) hε)
  have ha₀1 : a₀ ≤ 1 := min_le_left _ _
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hs : 0 < s.im := (isotropicRadialParameter_estimates α ε hα hε (hεδ.trans hδ1)).2.2.2.1
  have hG₀ : Continuous G₀ :=
    (actualTotalPhase_constrainedLine_contDiff s hs η τ ξ hη hτ.1 hξ.1 θ i j 0).continuous
  have hG : Continuous G := hG₀.sub continuous_const
  have hD : Continuous D :=
    actualProjectedPhase_constrainedLine_derivative_continuous s hs η τ ξ hη hτ.1 hξ.1 θ i j
  have hF : Continuous F :=
    actualExtremeJacobian_constrainedLine_continuous s hs η τ ξ hη hτ.1 hξ.1 θ i j
  have hproj (t : ℝ) : HasDerivAt (fun u => (frozenObliqueRotation * G u).re) (D t) t := by
    have hh := (actualTotalPhase_constrainedLine_hasDerivAt_any s hs η τ ξ hη hτ.1 hξ.1 θ i j t).sub_const
      (γ : ℂ)
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hh.const_mul frozenObliqueRotation)
  have hphase (t : ℝ) (ht : t ∈ Icc A B) :
      ‖G₀ t‖ ≤ K * N ∧ c * N * ε ≤ -(G₀ t).im := by
    have hf := hfiber ht
    have hθA : ∀ k, constrainedAngleLine θ i j t k ∈ Icc (-b - βA) βA := by
      intro k
      exact ⟨by linarith only [(hf.1 k).1, hβA], (hf.1 k).2.trans hβA'⟩
    exact (hatten N hN ε hε (hεδ.trans hδA') τ ξ ⟨hτ.1, hτ.2.trans hδA'⟩ hξ _ hθA).2
  have hdata (t : ℝ) (ht : t ∈ Icc A B) :
      0 < D t ∧ 0 ≤ F t ∧ F t / D t ≤ Q ∧ a₀ ≤ -(G t).im := by
    let Θ := constrainedAngleLine θ i j t
    have hf := hfiber ht
    have hΘ : ∀ k, Θ k ∈ Icc (-b) βR :=
      fun k => ⟨(hf.1 k).1, (hf.1 k).2.trans hβR'⟩
    have hgap : Θ i < Θ j := by
      have hh : r ≤ Θ j - Θ i := hf.2.2.2.1
      linarith only [hr, hh]
    have hrat := (hratio N hN ε hε (hεδ.trans hδR') τ ξ ⟨hτ.1, hτ.2.trans hδR'⟩ hξ Θ hΘ i j
      hf.2.1 hf.2.2.1 hgap).2
    refine ⟨hrat.1, norm_nonneg _, hrat.2.trans ?_, ?_⟩
    · have hdepth := positiveExtremeFiber_depth_bound hN θ i j b β r t hf j
      have hM : Θ j + b + ε ≤ 2 * T := by
        have hh : Θ j + b - μ ≤ 2 * r := (abs_le.mp hdepth).2
        dsimp [T]
        linarith only [hh, le_abs_self μ, abs_nonneg μ, hε]
      have hsqrt : Real.sqrt (Θ j + b + ε) ≤ Real.sqrt 2 * Real.sqrt T := by
        have hh := Real.sqrt_le_sqrt hM
        rwa [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)] at hh
      have hgapr : r ≤ Θ j - Θ i := hf.2.2.2.1
      calc
        _ ≤ R * (Real.sqrt 2 * Real.sqrt T) / r := by
          exact div_le_div₀ (by positivity)
            (mul_le_mul_of_nonneg_left hsqrt hR.le) hr hgapr
        _ = Q := by dsimp [Q]; ring
    · have hh := (min_le_right 1 (c * N * ε)).trans (hphase t ht).2
      simpa only [G, Complex.sub_im, Complex.ofReal_im, sub_zero] using hh
  have hmain := hcoarea G D F A B a₀ Q hAB ha₀ ha₀1 hQ hG hD hF
    (fun t _ => hproj t) hdata
  have hrange : 1 + ((frozenObliqueRotation * G B).re - (frozenObliqueRotation * G A).re) ≤
      (1 + 2 * K) * N := by
    have hA := (hphase A (left_mem_Icc.mpr hAB)).1
    have hB := (hphase B (right_mem_Icc.mpr hAB)).1
    have he : (frozenObliqueRotation * G B).re - (frozenObliqueRotation * G A).re =
        (frozenObliqueRotation * (G₀ B - G₀ A)).re := by
      dsimp only [G]
      rw [← Complex.sub_re, ← mul_sub]
      congr 2
      ring
    rw [he]
    have hh := (le_abs_self (frozenObliqueRotation * (G₀ B - G₀ A)).re).trans
      (Complex.abs_re_le_norm _)
    rw [norm_mul, frozenObliqueRotation_norm, one_mul] at hh
    have hnorm := norm_sub_le (G₀ B) (G₀ A)
    nlinarith only [hh, hnorm, hA, hB, hn]
  have hlog := particle_attenuation_log_cost c ε N hc hε (hεδ.trans hδ1) hN
  change 1 + |Real.log a₀| ≤ _ at hlog
  calc
    _ ≤ C₀ * Q * (1 + ((frozenObliqueRotation * G B).re - (frozenObliqueRotation * G A).re)) *
        (1 + |Real.log a₀|) := hmain
    _ ≤ C₀ * Q * ((1 + 2 * K) * N) * (1 + |Real.log a₀|) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrange (mul_nonneg hC₀.le hQ)) (by positivity)
    _ ≤ C₀ * Q * ((1 + 2 * K) * N) * ((1 + |Real.log c|) * (1 + |Real.log ε|)) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = _ := by dsimp [C, Q, T, μ]; ring

end IsingBulk.AnisoF002.Isotropic
