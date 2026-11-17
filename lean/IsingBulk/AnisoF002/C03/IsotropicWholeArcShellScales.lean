import IsingBulk.AnisoF002.C03.IsotropicWholeArcDerivative

/-!
# The sharp coordinate shell scale for every actual right tuple

The whole-arc derivative is integrated with the two genuine full
occupancies of the tuple. Thus every pair, including pairs across the
branch and endpoint slivers, obeys the frozen scale Delta=r/sqrt(T).
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric

theorem actualHomotopyRegular_eq_fixedCurve {N : ℕ} (s : ℂ) (η τ ξ : ℝ)
    (θ : Fin N → ℝ) (i : Fin N) :
    (actualHomotopyRegularTuple s η τ ξ θ).2 i =
      fixedOccupancyRegularCurve s η (ξ * τ) (actualUpperOccupancy η θ)
        (actualLowerOccupancy η θ) (θ i) := by
  change physicalRegularCoordinate (s, actualHomotopyAngle η τ ξ θ i) = _
  rw [actualHomotopyAngle_eq_fixedOccupancy]
  rfl

/-- The first estimate in frozen F002 `eq:iso-coordinate-scales`, now
for the actual whole right angular image with both endpoint slivers.
The constants precede N, all occupancies, every shell and every pair. -/
theorem exists_actual_whole_arc_shell_coordinate_scale (α b η : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α)
    (hη : 0 < η) (hwidth : 4 * η ≤ Real.sin b) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧
      ∀ (N : ℕ), 0 < N → ∀ (ε : ℝ), 0 < ε → ε ≤ δ →
      ∀ (τ ξ : ℝ), τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
      ∀ (θ : Fin N → ℝ), (∀ i, θ i ∈ Icc (-Real.pi - δ) δ) →
      ∀ r : ℝ, 0 < r → (∀ i j, |θ i - θ j| ≤ 2 * r) →
      ∀ i j : Fin N,
        ‖(actualHomotopyRegularTuple (isotropicRadialParameter α ε) η τ ξ θ).2 i -
          (actualHomotopyRegularTuple (isotropicRadialParameter α ε) η τ ξ θ).2 j‖ ≤
            C * r / Real.sqrt (|angularMean (fun k => θ k + b)| + r + ε) := by
  obtain ⟨δ, K, hδ, hδ1, hK, hderiv⟩ :=
    exists_fixedOccupancy_whole_arc_derivative α b η hα hb hpoint hη hwidth
  refine ⟨δ, 24 * K, hδ, hδ1, by positivity, ?_⟩
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
