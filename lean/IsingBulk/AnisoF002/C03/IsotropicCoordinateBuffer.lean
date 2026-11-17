import IsingBulk.AnisoF002.C03.IsotropicUniformBumpWindow
import IsingBulk.AnisoF002.C03.IsotropicWholeArcShellScales

/-!
# A complete coordinate shell buffer before the bump width

The geometric angular window is fixed before η. Integration still uses
both actual population fractions and the complete deformed coordinate.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set Metric

theorem exists_actual_whole_arc_coordinate_buffer (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b →
      ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ), 0 < N → ∀ (ε : ℝ), 0 < ε → ε ≤ δ →
      ∀ (τ ξ : ℝ), τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
      ∀ (θ : Fin N → ℝ), (∀ i, θ i ∈ Icc (-Real.pi - δ) δ) →
      ∀ r : ℝ, 0 < r → (∀ i j, |θ i - θ j| ≤ 2 * r) →
      ∀ i j : Fin N,
        ‖(actualHomotopyRegularTuple (isotropicRadialParameter α ε) η τ ξ θ).2 i -
          (actualHomotopyRegularTuple (isotropicRadialParameter α ε) η τ ξ θ).2 j‖ ≤
            C * r / Real.sqrt (|angularMean (fun k => θ k + b)| + r + ε) := by
  obtain ⟨δ, hδ, hδ1, hderivAll⟩ := exists_whole_arc_derivative_buffer α b hα hb hpoint
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro η hη hwidth
  obtain ⟨K, hK, hderiv⟩ := hderivAll η hη hwidth
  refine ⟨24 * K, by positivity, ?_⟩
  intro N hN ε hε hεδ τ ξ hτ hξ θ hθ r hr hdiam i j
  let μ := angularMean (fun k => θ k + b)
  let ρ := actualUpperOccupancy η θ
  let υ := actualLowerOccupancy η θ
  let g : ℝ → ℂ := fun u => fixedOccupancyRegularCurve (isotropicRadialParameter α ε)
    η (ξ * τ) ρ υ (u - b)
  have hρ : ρ ∈ Icc 0 1 := actualUpperOccupancy_mem_Icc hN η θ
  have hυ : υ ∈ Icc 0 1 := actualLowerOccupancy_mem_Icc hN η θ
  have hτξ : ξ * τ ∈ Icc 0 δ := by
    refine ⟨mul_nonneg hξ.1 hτ.1, ?_⟩
    exact (show ξ * τ ≤ τ by nlinarith only [hξ.2, hτ.1]).trans hτ.2
  have hloc (k : Fin N) : θ k + b ∈ Icc (μ - 2 * r) (μ + 2 * r) := by
    have hm := angularMean_distance_bound hN (fun l => θ l + b) (2 * r)
      (fun l m => by simpa only [add_sub_add_right_eq_sub] using hdiam l m) k
    exact ⟨by linarith only [(abs_le.mp hm).1], by linarith only [(abs_le.mp hm).2]⟩
  have hge (k : Fin N) : g (θ k + b) =
      (actualHomotopyRegularTuple (isotropicRadialParameter α ε) η τ ξ θ).2 k := by
    rw [actualHomotopyRegular_eq_fixedCurve]
    simp only [g, add_sub_cancel_right, ρ, υ]
  have hord (a z : Fin N) (haz : θ a ≤ θ z) :
      ‖g (θ z + b) - g (θ a + b)‖ ≤ 24 * K * r / Real.sqrt (|μ| + r + ε) := by
    apply norm_sub_le_branch_shell_of_le (by linarith only [haz]) hr hε hK.le (hloc a).1 (hloc z).2
    intro u hu
    have huθ : u - b ∈ Icc (-Real.pi - δ) δ := by
      exact ⟨by linarith only [hu.1, (hθ a).1], by linarith only [hu.2, (hθ z).2]⟩
    obtain ⟨hd, hn⟩ := hderiv ε hε hεδ (ξ * τ) ρ υ hτξ hρ hυ (u - b) huθ
    have hg : HasDerivAt g
        (fixedOccupancyRegularSlope (isotropicRadialParameter α ε) η (ξ * τ) ρ υ (u - b)) u := by
      simpa! only [g, Function.comp_def, id_eq, one_smul] using hd.scomp u ((hasDerivAt_id u).sub_const b)
    refine ⟨hg, ?_⟩
    simpa only [sub_add_cancel] using hn
  rcases le_total (θ i) (θ j) with hij | hji
  · have h := hord i j hij
    rw [hge, hge, norm_sub_rev] at h
    exact h
  · have h := hord j i hji
    rw [hge, hge] at h
    exact h


end IsingBulk.AnisoF002.Isotropic
