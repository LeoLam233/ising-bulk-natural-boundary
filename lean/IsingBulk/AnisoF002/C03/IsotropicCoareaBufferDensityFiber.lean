import IsingBulk.AnisoF002.C03.IsotropicCoareaBufferFullFiber
import IsingBulk.AnisoF002.C03.IsotropicFullDensityFiber

/-!
# All physical Jacobians on the actual fiber with independent geometric width
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set Metric MeasureTheory Filter

theorem exists_actual_full_density_fiber_integral_buffer (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b →
      ∃ δ C W : ℝ, 0 < δ ∧ δ ≤ β ∧ 0 < C ∧ 0 < W ∧
      ∀ (N : ℕ), 0 < N → ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
      ∀ (θ : Fin N → ℝ) (i j : Fin N), i ≠ j →
      ∀ r γ A B : ℝ, 0 < r → A ≤ B → Icc A B ⊆ fullExtremeFiber θ i j b β r →
        (∫ t in A..B, actualFullPhaseDensity (isotropicRadialParameter α ε) η τ ξ γ
          (constrainedAngleLine θ i j t)) ≤
        (C * N * Real.sqrt (|angularMean (fun k => θ k + b)| + r + ε) / r * (1 + |Real.log ε|)) *
          independentRemainingWeight W ε b θ i j := by
  obtain ⟨βF, hβF, hβF1, hFdata⟩ :=
    exists_actual_full_extreme_fiber_integral_buffer α b hα hb hpoint
  obtain ⟨βW, hβW, _, hWdata⟩ :=
    exists_actual_whole_arc_jacobian_weight_buffer α b hα hb hpoint
  let β := min βF βW
  have hβ : 0 < β := lt_min hβF hβW
  have hβF' : β ≤ βF := min_le_left _ _
  have hβW' : β ≤ βW := min_le_right _ _
  have hβ1 : β ≤ 1 := hβF'.trans hβF1
  refine ⟨β, hβ, hβ1, ?_⟩
  intro η hη hwidth
  obtain ⟨δF, C, hδF, _, hC, hbound⟩ := hFdata η hη hwidth
  obtain ⟨W, hW, hweight⟩ := hWdata η hη hwidth
  let δ := min δF β
  have hδ : 0 < δ := lt_min hδF hβ
  have hδF' : δ ≤ δF := min_le_left _ _
  have hδβ : δ ≤ β := min_le_right _ _
  have hδW' : δ ≤ βW := hδβ.trans hβW'
  have hδ1 : δ ≤ 1 := hδβ.trans hβ1
  refine ⟨δ, C, W, hδ, hδβ, hC, hW, ?_⟩
  intro N hN ε hε hεδ τ ξ hτ hξ θ i j hij r γ A B hr hAB hfiber
  let s := isotropicRadialParameter α ε
  let P := independentRemainingWeight W ε b θ i j
  have hP : 0 ≤ P := independentRemainingWeight_nonneg W ε b hW.le θ i j
  have hs : 0 < s.im := (isotropicRadialParameter_estimates α ε hα hε (hεδ.trans hδ1)).2.2.2.1
  have hpointwise (t : ℝ) (ht : t ∈ Icc A B) :
      actualFullPhaseDensity s η τ ξ γ (constrainedAngleLine θ i j t) ≤
        actualExtremeFiberDensity s η τ ξ γ θ i j t * P := by
    have hf := hfiber ht
    have hθW : ∀ k, constrainedAngleLine θ i j t k ∈ Icc (-Real.pi - βW) βW := by
      intro k
      exact ⟨by linarith only [(hf.1 k).1, hb.2, hβW'], (hf.1 k).2.trans hβW'⟩
    have hprod : (∏ k ∈ extremeRemainingIndices i j,
        ‖1 + actualPhaseSlope s η τ ξ (constrainedAngleLine θ i j t) k‖) ≤ P := by
      apply Finset.prod_le_prod₀ (fun _k _ => norm_nonneg _)
      intro k hk
      have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
      have hki : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
      have hh := hweight N hN ε hε (hεδ.trans hδW') τ ξ ⟨hτ.1, hτ.2.trans hδW'⟩ hξ _ hθW k
      rw [constrainedAngleLine_other θ i j k hki hkj t] at hh
      simpa only [branchWeight, mul_one_div] using hh
    rw [actualFullPhaseDensity_split_extremes s η τ ξ γ θ i j hij t]
    exact mul_le_mul_of_nonneg_left hprod (div_nonneg (norm_nonneg _) (norm_nonneg _))
  have hproper : Icc A B ⊆ fullExtremeFiber θ i j b βF r := by
    intro t ht
    have hf := hfiber ht
    refine ⟨?_, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2⟩
    intro k
    exact ⟨by linarith only [(hf.1 k).1, hβF'], (hf.1 k).2.trans hβF'⟩
  have hleft := actualFullPhaseDensity_constrainedLine_continuous s hs η τ ξ γ hη hτ.1 hξ.1 θ i j hij
  have hright := (actualExtremeFiberDensity_continuous s hs η τ ξ γ hη hτ.1 hξ.1 θ i j).mul_const P
  have hmain := intervalIntegral.integral_mono_on (μ := volume) hAB (hleft.intervalIntegrable A B)
    (hright.intervalIntegrable A B) hpointwise
  rw [intervalIntegral.integral_mul_const] at hmain
  exact hmain.trans (mul_le_mul_of_nonneg_right
    (hbound N hN ε hε (hεδ.trans hδF') τ ξ ⟨hτ.1, hτ.2.trans hδF'⟩ hξ θ i j r γ A B hr hAB hproper) hP)

end IsingBulk.AnisoF002.Isotropic
