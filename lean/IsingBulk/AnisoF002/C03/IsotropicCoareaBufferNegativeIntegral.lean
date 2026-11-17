import IsingBulk.AnisoF002.C03.IsotropicCoareaBufferNegative
import IsingBulk.AnisoF002.C03.IsotropicActualNegativeCoarea

/-!
# The entire negative-minimum fiber integral on the geometric buffer
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set Metric MeasureTheory

theorem exists_actual_negative_extreme_integral_buffer (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b →
      ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ), 0 < N → ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
      ∀ (θ : Fin N → ℝ) (i j : Fin N) (r γ A B : ℝ), 0 < r → A ≤ B →
        Icc A B ⊆ negativeExtremeFiber θ i j b δ r →
        (∫ t in A..B, actualExtremeFiberDensity (isotropicRadialParameter α ε) η τ ξ γ θ i j t) ≤
          C * Real.sqrt (|angularMean (fun k => θ k + b)| + r + ε) / r *
            (1 + |Real.log ε|) := by
  obtain ⟨δ, hδ, hδ1, hdata⟩ :=
    exists_actual_negative_extreme_kernel_buffer α b hα hb hpoint
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro η hη hwidth
  obtain ⟨C₀, hC₀, hpointwise⟩ := hdata η hη hwidth
  obtain ⟨C₁, hC₁, hsliceIntegral⟩ := exists_reciprocal_extreme_slice_integral
    (Real.pi + 1) (by positivity)
  let C := C₀ * C₁
  refine ⟨C, mul_pos hC₀ hC₁, ?_⟩
  intro N hN ε hε hεδ τ ξ hτ hξ θ i j r γ A B hr hAB hfiber
  let s := isotropicRadialParameter α ε
  let x := θ i + b
  let y := θ j + b
  let T := |angularMean (fun k => θ k + b)| + r + ε
  have hT : 0 < T := by dsimp [T]; positivity
  have hs : 0 < s.im := (isotropicRadialParameter_estimates α ε hα hε (hεδ.trans hδ1)).2.2.2.1
  have hij : i ≠ j := by
    intro he
    have hh := (hfiber (left_mem_Icc.mpr hAB)).1.2.2.2.1
    rw [he, sub_self] at hh
    linarith only [hr, hh]
  have hslice (t : ℝ) (ht : t ∈ Icc A B) : |x + t| ≤ Real.pi + 1 ∧ |y - t| ≤ Real.pi + 1 := by
    have hf := (hfiber ht).1
    have hcoord (k : Fin N) : |constrainedAngleLine θ i j t k + b| ≤ Real.pi + 1 := by
      rw [abs_le]
      constructor <;> linarith only [(hf.1 k).1, (hf.1 k).2, hδ1, hb.1, hb.2, Real.pi_pos]
    have hi := hcoord i
    have hj := hcoord j
    rw [constrainedAngleLine_first θ i j hij t] at hi
    rw [constrainedAngleLine_last θ i j hij t] at hj
    constructor
    · simpa only [x, add_right_comm (θ i) t b] using hi
    · simpa only [y, show θ j - t + b = θ j + b - t by ring] using hj
  have hpoint (t : ℝ) (ht : t ∈ Icc A B) :
      actualExtremeFiberDensity s η τ ξ γ θ i j t ≤
        (C₀ / Real.sqrt r) *
          (reciprocalAngularDepth ε (x + t) + reciprocalAngularDepth ε (y - t)) := by
    let Θ := constrainedAngleLine θ i j t
    let a := |Θ i + b| + ε
    let c := |Θ j + b| + ε
    have hf := hfiber ht
    have hθ : ∀ k, Θ k ∈ Icc (-b - δ) δ := by
      intro k
      exact ⟨by linarith only [(hf.1.1 k).1], (hf.1.1 k).2⟩
    have hk := hpointwise N hN ε hε hεδ τ ξ hτ hξ Θ hθ i j γ hf.2
    have ha : 0 < a := by dsimp [a]; positivity
    have hc : 0 < c := by dsimp [c]; positivity
    have hac : r ≤ a + c := by
      have hgap : r ≤ Θ j - Θ i := hf.1.2.2.2.1
      have hai := neg_le_abs (Θ i + b)
      have haj := le_abs_self (Θ j + b)
      dsimp [a, c]
      linarith only [hgap, hai, haj, hε]
    have hrecip := reciprocal_pair_depth_bound a c r ha hc hr hac
    change actualExtremeFiberDensity s η τ ξ γ θ i j t ≤ C₀ / (a * Real.sqrt c) at hk
    have hbase : C₀ / (a * Real.sqrt c) ≤ (C₀ / Real.sqrt r) * (1 / a + 1 / c) := by
      have hh := mul_le_mul_of_nonneg_left hrecip hC₀.le
      convert hh using 1 <;> ring
    apply hk.trans (hbase.trans_eq ?_)
    dsimp only [a, c, Θ]
    rw [constrainedAngleLine_first θ i j hij t, constrainedAngleLine_last θ i j hij t]
    simp only [reciprocalAngularDepth, x, y, add_right_comm (θ i) t b,
      show θ j - t + b = θ j + b - t by ring]
  have hcont := actualExtremeFiberDensity_continuous s hs η τ ξ γ hη hτ.1 hξ.1 θ i j
  have hw := reciprocalAngularDepth_continuous ε hε
  have hmajorCont : Continuous (fun t : ℝ => (C₀ / Real.sqrt r) *
      (reciprocalAngularDepth ε (x + t) + reciprocalAngularDepth ε (y - t))) :=
    continuous_const.mul ((hw.comp (continuous_const.add continuous_id)).add
      (hw.comp (continuous_const.sub continuous_id)))
  have hmain := intervalIntegral.integral_mono_on (μ := volume) hAB (hcont.intervalIntegrable A B)
    (hmajorCont.intervalIntegrable A B) hpoint
  rw [intervalIntegral.integral_const_mul] at hmain
  have hlog := hsliceIntegral ε hε (hεδ.trans hδ1) x y A B hAB hslice
  have hscale : 1 / Real.sqrt r ≤ Real.sqrt T / r := by
    apply (div_le_div_iff₀ (Real.sqrt_pos.mpr hr) hr).mpr
    have hh := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt
      (show r ≤ T by dsimp [T]; linarith only [abs_nonneg (angularMean (fun k => θ k + b)), hε]))
      (Real.sqrt_nonneg r)
    rw [Real.mul_self_sqrt hr.le] at hh
    simpa only [one_mul] using hh
  calc
    _ ≤ (C₀ / Real.sqrt r) *
        (∫ t in A..B, reciprocalAngularDepth ε (x + t) + reciprocalAngularDepth ε (y - t)) := hmain
    _ ≤ (C₀ / Real.sqrt r) * (C₁ * (1 + |Real.log ε|)) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = C * (1 / Real.sqrt r) * (1 + |Real.log ε|) := by dsimp [C]; ring
    _ ≤ C * (Real.sqrt T / r) * (1 + |Real.log ε|) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscale (mul_pos hC₀ hC₁).le) (by positivity)
    _ = _ := by dsimp [T]; ring

end IsingBulk.AnisoF002.Isotropic
