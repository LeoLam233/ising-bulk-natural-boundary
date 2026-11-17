import IsingBulk.AnisoF002.C03.IsotropicActualAttenuation
import IsingBulk.AnisoF002.C03.IsotropicActualExtremeRatio
import IsingBulk.AnisoF002.C03.IsotropicPositiveExtremeFiber
import IsingBulk.AnisoF002.C03.IsotropicFiberRegularity
import IsingBulk.AnisoF002.C03.IsotropicObliqueCoarea
import IsingBulk.AnisoF002.C03.IsotropicBranchCoordinateScales

/-!
# The actual positive extreme-coordinate coarea integral

The physical constrained phase, both changing populations, complete
extreme Jacobian factors and full product denominator are integrated
on the actual fiber. The bound has the frozen shell scale, the linear
particle-range cost, and the logarithmic radial cost. An arbitrary real
phase shift includes both physical signs and every winding.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric MeasureTheory

theorem constrainedAngleLine_shifted_mean {N : ℕ} (θ : Fin N → ℝ) (i j : Fin N) (b t : ℝ) :
    angularMean (fun k => constrainedAngleLine θ i j t k + b) =
      angularMean (fun k => θ k + b) := by
  simp only [angularMean, Finset.sum_add_distrib, constrainedAngleLine_sum]

theorem positiveExtremeFiber_depth_bound {N : ℕ} (hN : 0 < N)
    (θ : Fin N → ℝ) (i j : Fin N) (b δ r t : ℝ)
    (ht : t ∈ positiveExtremeFiber θ i j b δ r) (k : Fin N) :
    |constrainedAngleLine θ i j t k + b - angularMean (fun l => θ l + b)| ≤ 2 * r := by
  have hdiam (l m : Fin N) :
      |(constrainedAngleLine θ i j t l + b) - (constrainedAngleLine θ i j t m + b)| ≤ 2 * r := by
    rw [abs_le]
    have hlmin := ht.2.1 l
    have hmmin := ht.2.1 m
    have hlmax := ht.2.2.1 l
    have hmmax := ht.2.2.1 m
    have hgap := ht.2.2.2.2
    constructor <;> linarith only [hlmin, hmmin, hlmax, hmmax, hgap]
  have hh := angularMean_distance_bound hN (fun l => constrainedAngleLine θ i j t l + b) (2 * r) hdiam k
  simpa only [constrainedAngleLine_shifted_mean] using hh

def actualExtremeFiberDensity {N : ℕ} (s : ℂ) (η τ ξ γ : ℝ)
    (θ : Fin N → ℝ) (i j : Fin N) (t : ℝ) : ℝ :=
  ‖(1 + actualPhaseSlope s η τ ξ (constrainedAngleLine θ i j t) i) *
      (1 + actualPhaseSlope s η τ ξ (constrainedAngleLine θ i j t) j)‖ /
    ‖1 - Complex.exp (-Complex.I *
      (actualTotalPhase η τ ξ (s, constrainedAngleLine θ i j t) - (γ : ℂ)))‖

/-- Positive-minimum half of frozen F002's extreme-coordinate coarea.
The estimate is on the actual fiber (or any closed subinterval), with
the exact angular mean retained. Its constants precede particle number,
the shell, all full populations, and the phase shift. -/
theorem exists_actual_positive_extreme_integral (α b η : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α)
    (hη : 0 < η) (hwidth : 4 * η ≤ Real.sin b) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧
      ∀ (N : ℕ), 0 < N → ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
      ∀ (θ : Fin N → ℝ) (i j : Fin N) (r γ A B : ℝ), 0 < r → A ≤ B →
        Icc A B ⊆ positiveExtremeFiber θ i j b δ r →
        (∫ t in A..B, actualExtremeFiberDensity (isotropicRadialParameter α ε) η τ ξ γ θ i j t) ≤
          C * N * Real.sqrt (|angularMean (fun k => θ k + b)| + r + ε) / r *
            (1 + |Real.log ε|) := by
  obtain ⟨δR, R, hδR, hδR1, hR, hratio⟩ :=
    exists_actual_constrained_extreme_ratio α b η hα hb hpoint hη hwidth
  obtain ⟨δA, K, c, hδA, _, hK, hc, hatten⟩ :=
    exists_actual_right_phase_attenuation α b η hα hb hpoint hη
  obtain ⟨C₀, hC₀, hcoarea⟩ := exists_oblique_phase_fiber_integral_bound
  let δ := min δR δA
  let C := C₀ * R * Real.sqrt 2 * (1 + 2 * K) * (1 + |Real.log c|)
  have hδ : 0 < δ := lt_min hδR hδA
  have hδR' : δ ≤ δR := min_le_left _ _
  have hδA' : δ ≤ δA := min_le_right _ _
  have hδ1 : δ ≤ 1 := hδR'.trans hδR1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨δ, C, hδ, hδ1, hC, ?_⟩
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
    have hθA : ∀ k, constrainedAngleLine θ i j t k ∈ Icc (-b - δA) δA := by
      intro k
      exact ⟨by linarith only [(hf.1 k).1, hδA], (hf.1 k).2.trans hδA'⟩
    exact (hatten N hN ε hε (hεδ.trans hδA') τ ξ ⟨hτ.1, hτ.2.trans hδA'⟩ hξ _ hθA).2
  have hdata (t : ℝ) (ht : t ∈ Icc A B) :
      0 < D t ∧ 0 ≤ F t ∧ F t / D t ≤ Q ∧ a₀ ≤ -(G t).im := by
    let Θ := constrainedAngleLine θ i j t
    have hf := hfiber ht
    have hΘ : ∀ k, Θ k ∈ Icc (-b) δR :=
      fun k => ⟨(hf.1 k).1, (hf.1 k).2.trans hδR'⟩
    have hgap : Θ i < Θ j := by
      have hh : r ≤ Θ j - Θ i := hf.2.2.2.1
      linarith only [hr, hh]
    have hrat := (hratio N hN ε hε (hεδ.trans hδR') τ ξ ⟨hτ.1, hτ.2.trans hδR'⟩ hξ Θ hΘ i j
      hf.2.1 hf.2.2.1 hgap).2
    refine ⟨hrat.1, norm_nonneg _, hrat.2.trans ?_, ?_⟩
    · have hdepth := positiveExtremeFiber_depth_bound hN θ i j b δ r t hf j
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
