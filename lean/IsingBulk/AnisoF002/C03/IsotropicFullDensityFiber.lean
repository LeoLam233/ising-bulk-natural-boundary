import IsingBulk.AnisoF002.C03.IsotropicActualFullFiberCoarea

/-!
# The full physical Jacobian density on a true extreme fiber

All remaining coordinates are bounded by independent integrable branch
weights only after the two actual extrema have been integrated. Their
phase slopes still contain the full changing populations. The measure
is ordinary real angular Lebesgue measure throughout.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric MeasureTheory

def extremeRemainingIndices {N : ℕ} (i j : Fin N) : Finset (Fin N) :=
  (Finset.univ.erase i).erase j

theorem prod_split_extreme_indices {N : ℕ} (i j : Fin N) (hij : i ≠ j) (f : Fin N → ℝ) :
    (∏ k, f k) = f i * f j * ∏ k ∈ extremeRemainingIndices i j, f k := by
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i)]
  rw [← Finset.mul_prod_erase (Finset.univ.erase i) f
    (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)]
  rw [mul_assoc]
  rfl

theorem extremeRemainingIndices_card {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    (extremeRemainingIndices i j).card = N - 2 := by
  rw [extremeRemainingIndices, Finset.card_erase_of_mem
    (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩),
    Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  omega

def actualFullPhaseDensity {N : ℕ} (s : ℂ) (η τ ξ γ : ℝ) (θ : Fin N → ℝ) : ℝ :=
  (∏ k, ‖1 + actualPhaseSlope s η τ ξ θ k‖) /
    ‖1 - Complex.exp (-Complex.I * (actualTotalPhase η τ ξ (s, θ) - (γ : ℂ)))‖

theorem actualFullPhaseDensity_nonneg {N : ℕ} (s : ℂ) (η τ ξ γ : ℝ) (θ : Fin N → ℝ) :
    0 ≤ actualFullPhaseDensity s η τ ξ γ θ :=
  div_nonneg (Finset.prod_nonneg (fun _k _ => norm_nonneg _)) (norm_nonneg _)

theorem actualFullPhaseDensity_split_extremes {N : ℕ}
    (s : ℂ) (η τ ξ γ : ℝ) (θ : Fin N → ℝ) (i j : Fin N) (hij : i ≠ j) (t : ℝ) :
    actualFullPhaseDensity s η τ ξ γ (constrainedAngleLine θ i j t) =
      actualExtremeFiberDensity s η τ ξ γ θ i j t *
        ∏ k ∈ extremeRemainingIndices i j, ‖1 + actualPhaseSlope s η τ ξ (constrainedAngleLine θ i j t) k‖ := by
  unfold actualFullPhaseDensity actualExtremeFiberDensity
  rw [prod_split_extreme_indices i j hij, norm_mul]
  ring

theorem actualFullPhaseDensity_constrainedLine_continuous {N : ℕ}
    (s : ℂ) (hs : 0 < s.im) (η τ ξ γ : ℝ) (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ)
    (θ : Fin N → ℝ) (i j : Fin N) (hij : i ≠ j) :
    Continuous (fun t : ℝ => actualFullPhaseDensity s η τ ξ γ (constrainedAngleLine θ i j t)) := by
  rw [funext (actualFullPhaseDensity_split_extremes s η τ ξ γ θ i j hij)]
  apply (actualExtremeFiberDensity_continuous s hs η τ ξ γ hη hτ hξ θ i j).mul
  apply continuous_finsetProd
  intro k _
  exact (continuous_const.add ((actualPhaseSlope_angles_continuous s hs η τ ξ hη hτ hξ k).comp
    (constrainedAngleLine_contDiff θ i j 0).continuous)).norm

def independentRemainingWeight {N : ℕ} (W ε b : ℝ) (θ : Fin N → ℝ) (i j : Fin N) : ℝ :=
  ∏ k ∈ extremeRemainingIndices i j, W * branchWeight ε (θ k + b)

theorem independentRemainingWeight_nonneg {N : ℕ} (W ε b : ℝ) (hW : 0 ≤ W)
    (θ : Fin N → ℝ) (i j : Fin N) : 0 ≤ independentRemainingWeight W ε b θ i j :=
  Finset.prod_nonneg (fun k _ => mul_nonneg hW (branchWeight_nonneg ε (θ k + b)))

theorem independentRemainingWeight_factor {N : ℕ} (W ε b : ℝ)
    (θ : Fin N → ℝ) (i j : Fin N) (hij : i ≠ j) :
    independentRemainingWeight W ε b θ i j =
      W ^ (N - 2) * ∏ k ∈ extremeRemainingIndices i j, branchWeight ε (θ k + b) := by
  rw [independentRemainingWeight, Finset.prod_mul_distrib, Finset.prod_const,
    extremeRemainingIndices_card i j hij]

/-- Actual complete fiber density, with independent envelopes for
exactly the N-2 non-extreme Jacobian factors. The constants precede N. -/
theorem exists_actual_full_density_fiber_integral (α b η : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α)
    (hη : 0 < η) (hwidth : 4 * η ≤ Real.sin b) :
    ∃ δ C W : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧ 0 < W ∧
      ∀ (N : ℕ), 0 < N → ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
      ∀ (θ : Fin N → ℝ) (i j : Fin N), i ≠ j →
      ∀ r γ A B : ℝ, 0 < r → A ≤ B → Icc A B ⊆ fullExtremeFiber θ i j b δ r →
        (∫ t in A..B, actualFullPhaseDensity (isotropicRadialParameter α ε) η τ ξ γ
          (constrainedAngleLine θ i j t)) ≤
        (C * N * Real.sqrt (|angularMean (fun k => θ k + b)| + r + ε) / r * (1 + |Real.log ε|)) *
          independentRemainingWeight W ε b θ i j := by
  obtain ⟨δF, C, hδF, hδF1, hC, hbound⟩ :=
    exists_actual_full_extreme_fiber_integral α b η hα hb hpoint hη hwidth
  obtain ⟨δW, W, hδW, _, hW, hweight⟩ :=
    exists_actual_whole_arc_jacobian_weight α b η hα hb hpoint hη hwidth
  let δ := min δF δW
  have hδ : 0 < δ := lt_min hδF hδW
  have hδF' : δ ≤ δF := min_le_left _ _
  have hδW' : δ ≤ δW := min_le_right _ _
  have hδ1 : δ ≤ 1 := hδF'.trans hδF1
  refine ⟨δ, C, W, hδ, hδ1, hC, hW, ?_⟩
  intro N hN ε hε hεδ τ ξ hτ hξ θ i j hij r γ A B hr hAB hfiber
  let s := isotropicRadialParameter α ε
  let P := independentRemainingWeight W ε b θ i j
  have hP : 0 ≤ P := independentRemainingWeight_nonneg W ε b hW.le θ i j
  have hs : 0 < s.im := (isotropicRadialParameter_estimates α ε hα hε (hεδ.trans hδ1)).2.2.2.1
  have hpointwise (t : ℝ) (ht : t ∈ Icc A B) :
      actualFullPhaseDensity s η τ ξ γ (constrainedAngleLine θ i j t) ≤
        actualExtremeFiberDensity s η τ ξ γ θ i j t * P := by
    have hf := hfiber ht
    have hθW : ∀ k, constrainedAngleLine θ i j t k ∈ Icc (-Real.pi - δW) δW := by
      intro k
      exact ⟨by linarith only [(hf.1 k).1, hb.2, hδW'], (hf.1 k).2.trans hδW'⟩
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
  have hproper : Icc A B ⊆ fullExtremeFiber θ i j b δF r := by
    intro t ht
    have hf := hfiber ht
    refine ⟨?_, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2⟩
    intro k
    exact ⟨by linarith only [(hf.1 k).1, hδF'], (hf.1 k).2.trans hδF'⟩
  have hleft := actualFullPhaseDensity_constrainedLine_continuous s hs η τ ξ γ hη hτ.1 hξ.1 θ i j hij
  have hright := (actualExtremeFiberDensity_continuous s hs η τ ξ γ hη hτ.1 hξ.1 θ i j).mul_const P
  have hmain := intervalIntegral.integral_mono_on (μ := volume) hAB (hleft.intervalIntegrable A B)
    (hright.intervalIntegrable A B) hpointwise
  rw [intervalIntegral.integral_mul_const] at hmain
  exact hmain.trans (mul_le_mul_of_nonneg_right
    (hbound N hN ε hε (hεδ.trans hδF') τ ξ ⟨hτ.1, hτ.2.trans hδF'⟩ hξ θ i j r γ A B hr hAB hproper) hP)

end IsingBulk.AnisoF002.Isotropic
