import IsingBulk.AnisoF002.C03.RegularIsotropicAnchorCompleteTail
import IsingBulk.AnisoF002.C03.RegularIsotropicMixedCompleteTail
import IsingBulk.AnisoF002.C03.IsotropicCompactDerivativePartition
import IsingBulk.AnisoF002.C03.IsotropicNonresonantFiniteCoefficient
import IsingBulk.AnisoF002.C03.IsotropicFirstCompactMean
import IsingBulk.AnisoF002.C03.IsotropicFirstCutoffGeometry

/-!
# Constructed common physical partition for every finite particle

The data below contain actual cutoffs, actual full coefficients and
their checked bounds. They are constructed from the original boundary
geometry. Their buffer is strictly below alpha and pi-b, so the exact
lower compact-mean set is inside (-pi,pi) and excludes +alpha.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set Filter

structure ActualFinitePartitionControl (α b : ℝ) where
  eta : ℝ
  tau : ℝ
  cutWidth : ℝ
  sliver : ℝ
  buffer : ℝ
  radius : ℝ
  eta_pos : 0 < eta
  tau_pos : 0 < tau
  buffer_pos : 0 < buffer
  buffer_lt_alpha : buffer < α
  buffer_lt_pi_sub : buffer < Real.pi - b
  radius_pos : 0 < radius
  radius_le_one : radius ≤ 1
  cutoff : RightCutoffGeometry b cutWidth sliver
  cutWidth_le : cutWidth ≤ buffer
  sliver_le : sliver + cutWidth / 2 ≤ buffer
  partition : ∀ n : ℕ, ∀ phase : ℝ, phase = 0 ∨ phase = Real.pi →
    ∀ σ : ℂ, σ = 1 ∨ σ = -1 → ∀ j : ℕ, ∀ ε ∈ Ioo 0 radius,
    iteratedDeriv j (isotropicFullParticleCoefficient (n + 1) phase σ) (isotropicRadialParameter α ε) =
      iteratedDeriv j (mixedPhysicalCoefficient (n + 1) eta tau phase σ) (isotropicRadialParameter α ε) +
      2 * ((∑ k ∈ admissibleRightLifts (n + 2) b buffer phase,
        iteratedDeriv j (compactMeanPhysicalCoefficient (n + 1) eta tau 1 b cutWidth sliver
          (constrainedRightMean (n + 2) b phase k - b) σ) (isotropicRadialParameter α ε)) +
        ∑ a : Fin (n + 2), iteratedDeriv j (actualWeightedParticleIntegral eta tau 1 σ
          (actualLowerAnchorCutoff eta b cutWidth sliver a) phase) (isotropicRadialParameter α ε))
  mixed_bound : ∀ n j : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ phase : ℝ, ∀ σ : ℂ, ‖σ‖ ≤ 1 →
    ∀ ε ∈ Ioo 0 radius,
    ‖iteratedDeriv j (mixedPhysicalCoefficient (n + 1) eta tau phase σ)
      (isotropicRadialParameter α ε)‖ ≤ A
  anchor_bound : ∀ n j : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ phase : ℝ, ∀ σ : ℂ, ‖σ‖ ≤ 1 →
    ∀ ε ∈ Ioo 0 radius,
    originalAnchorJetNorm j n eta tau b cutWidth sliver phase σ (isotropicRadialParameter α ε) ≤ A
  nonresonant_bound : ∀ n : ℕ, ∀ μ : ℝ, ∀ σ : ℂ, σ = 1 ∨ σ = -1 →
    -1 < 2 * Real.cos α - Real.cos μ → 2 * Real.cos α - Real.cos μ ≠ 1 →
    1 - σ * upperBoundaryRoot (2 * Real.cos α - Real.cos μ) ^ (n + 2) ≠ 0 →
    ∀ j : ℕ, ∃ e A : ℝ, 0 < e ∧ e ≤ radius ∧ 0 < A ∧ ∀ ε ∈ Ioo 0 e,
      ‖iteratedDeriv j (compactMeanPhysicalCoefficient (n + 1) eta tau 1 b cutWidth sliver μ σ)
        (isotropicRadialParameter α ε)‖ ≤ A * (1 + |Real.log ε|)
  first_limit : ∀ n j l : ℕ, 0 < l → 2 * j + 2 = n + 1 + 2 * (n + 2).choose 2 + l →
    ∀ σ : ℂ, σ = 1 ∨ σ = -1 →
    σ * Complex.exp (-(((n + 2 : ℕ) : ℂ) * ((α : ℂ) * Complex.I))) = 1 →
    Tendsto (fun s : ℝ => (s : ℂ) ^ l *
      iteratedDeriv j (compactMeanPhysicalCoefficient (n + 1) eta tau 1 b cutWidth sliver (-α) σ)
        (isotropicRadialParameter α (s ^ 2))) (𝓝[>] (0 : ℝ))
      (𝓝 (isotropicFirstChartAmplitude (n + 1) α j))

theorem exists_actual_finite_partition_control (α b : ℝ)
    (hα : 0 < α) (hhalf : α < Real.pi / 2) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    Nonempty (ActualFinitePartitionControl α b) := by
  have hπ : α < Real.pi := hhalf.trans (by linarith only [Real.pi_pos])
  have hαb := isotropic_first_angle_lt_branch ⟨hα, hπ⟩ hb hpoint
  obtain ⟨βn, hβn, _, hnonres⟩ := exists_actual_nonresonant_compact_mean_bound α b ⟨hα, hπ⟩ hb hpoint
  obtain ⟨βf, hβf, _, hfirst⟩ := exists_actual_first_compact_mean_scaled_limit α b hα hhalf hb hpoint hαb
  let β := min βn (min βf (min (α / 2) ((Real.pi - b) / 2)))
  have hβ : 0 < β := lt_min hβn (lt_min hβf (lt_min (by positivity) (by linarith only [hb.2])))
  have hβn' : β ≤ βn := min_le_left _ _
  have hβf' : β ≤ βf := (min_le_right _ _).trans (min_le_left _ _)
  have hβα : β ≤ α / 2 := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hβπ : β ≤ (Real.pi - b) / 2 := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hβα' : β < α := by linarith only [hβα, hα]
  have hβπ' : β < Real.pi - b := by linarith only [hβπ, hb.2]
  let δB := β / 4
  have hδB : 0 < δB := by positivity
  have hleft : b + δB < Real.pi := by dsimp [δB]; linarith only [hβπ', hβ]
  obtain ⟨βa, hβa, _, hanchor⟩ :=
    exists_actual_anchor_summable_jet_majorants α b δB ⟨hα, hπ⟩ hb hpoint hδB hleft
  let ρ := min βa (β / 4)
  have hρ : 0 < ρ := lt_min hβa (by positivity)
  have hρa : ρ ≤ βa := min_le_left _ _
  have hρβ : ρ ≤ β / 4 := min_le_right _ _
  have hcut : RightCutoffGeometry b δB ρ :=
    ⟨hb.1, hδB, hρ, hleft, by dsimp [δB]; linarith only [hρβ, hβπ', hb.1, hβ]⟩
  have hδBβ : δB ≤ β := by dsimp [δB]; linarith only [hβ]
  have hρBβ : ρ + δB / 2 ≤ β := by dsimp [δB]; linarith only [hρβ, hβ]
  have hsinb : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi hb.1 hb.2
  have hsinρ : 0 < Real.sin (ρ / 2) := Real.sin_pos_of_pos_of_lt_pi (by positivity)
    (by linarith only [hρβ, hβπ', hb.1, Real.pi_pos])
  let η := min (Real.sin b / 8) (Real.sin (ρ / 2) / 4)
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hηb : η ≤ Real.sin b / 8 := min_le_left _ _
  have hηρ : η ≤ Real.sin (ρ / 2) / 4 := min_le_right _ _
  have hwidth : 4 * η ≤ Real.sin b := by linarith only [hηb, hsinb]
  have hgap : 2 * η ≤ Real.sin (ρ / 2) := by linarith only [hηρ, hsinρ]
  have hηα := isotropic_first_plateau_width ⟨hα, hπ⟩ hb hpoint hwidth
  obtain ⟨δn, hδn, _, hN⟩ := hnonres η hη hwidth
  obtain ⟨δf, hδf, _, hF⟩ := hfirst η hη hwidth hηα
  obtain ⟨δa, hδa, _, hA⟩ := hanchor ρ hρ hρa hcut η hη hwidth hgap
  obtain ⟨δm, hδm, _, hM⟩ := exists_actual_mixed_summable_jet_majorants α b η ⟨hα, hπ⟩ hb hpoint hη hwidth
  obtain ⟨Δ, hΔ, hpart⟩ := exists_actual_complete_compact_derivative_partition η hη
  let δ := min 1 (min δn (min δf (min δa (min δm Δ))))
  have hδ : 0 < δ := lt_min zero_lt_one (lt_min hδn (lt_min hδf (lt_min hδa (lt_min hδm hΔ))))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδn' : δ ≤ δn := (min_le_right _ _).trans (min_le_left _ _)
  have hδf' : δ ≤ δf := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hδa' : δ ≤ δa := (((min_le_right _ _).trans (min_le_right _ _)).trans
    (min_le_right _ _)).trans (min_le_left _ _)
  have hδm' : δ ≤ δm := ((((min_le_right _ _).trans (min_le_right _ _)).trans
    (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hδΔ : δ ≤ Δ := ((((min_le_right _ _).trans (min_le_right _ _)).trans
    (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)
  let τ := δ / 2
  have hτ : 0 < τ := by positivity
  have hτδ : τ ≤ δ := by dsimp [τ]; linarith only [hδ]
  refine ⟨{
    eta := η
    tau := τ
    cutWidth := δB
    sliver := ρ
    buffer := β
    radius := δ
    eta_pos := hη
    tau_pos := hτ
    buffer_pos := hβ
    buffer_lt_alpha := hβα'
    buffer_lt_pi_sub := hβπ'
    radius_pos := hδ
    radius_le_one := hδ1
    cutoff := hcut
    cutWidth_le := hδBβ
    sliver_le := hρBβ
    partition := ?_
    mixed_bound := ?_
    anchor_bound := ?_
    nonresonant_bound := ?_
    first_limit := ?_ }⟩
  · intro n phase hphase σ hσ j ε hε
    have hσnorm : ‖σ‖ ≤ 1 := by rcases hσ with rfl | rfl <;> norm_num
    exact hpart n τ ⟨hτ.le, hτδ.trans hδΔ⟩ b δB ρ β phase hcut hδBβ hρBβ hphase σ _ hσnorm
      (isotropicRadialParameter_estimates α ε ⟨hα, hπ⟩ hε.1 (hε.2.le.trans hδ1)).2.2.2.1 j
  · intro n j
    obtain ⟨M, hM0, _, hMb⟩ := hM τ hτ (hτδ.trans hδm') j
    refine ⟨M (n + 1), hM0 _, ?_⟩
    intro phase σ hσ ε hε
    exact hMb (n + 1) ε hε.1 (hε.2.le.trans hδm') phase σ hσ
  · intro n j
    obtain ⟨M, hM0, _, hMb⟩ := hA j
    refine ⟨M n, hM0 _, ?_⟩
    intro phase σ hσ ε hε
    exact hMb n σ hσ τ ⟨hτ.le, hτδ.trans hδa'⟩ phase ε ⟨hε.1, hε.2.trans_le hδa'⟩
  · intro n μ σ hσ hx hx1 hden j
    obtain ⟨e, A, he, _, hA, hbnd⟩ := hN δB ρ hcut (hδBβ.trans hβn') (hρBβ.trans hβn')
      n τ ⟨hτ.le, hτδ.trans hδn'⟩ 1 (by norm_num) μ σ hσ hx hx1 hden j
    refine ⟨min δ e, A, lt_min hδ he, min_le_left _ _, hA, ?_⟩
    intro ε hε
    exact hbnd ε ⟨hε.1, hε.2.trans_le (min_le_right _ _)⟩
  · intro n j l hl hdegree σ hσ hres
    exact hF δB ρ hcut (hδBβ.trans hβf') (hρBβ.trans hβf') n j l hl hdegree σ hσ hres
      τ ⟨hτ.le, hτδ.trans hδf'⟩ 1 (by norm_num)

end IsingBulk.AnisoF002.Isotropic
