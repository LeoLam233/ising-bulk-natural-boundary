import IsingBulk.Tail.AllBranchExteriorKernelScalarBounds
import IsingBulk.Tail.ScaleInclusions
import IsingBulk.Tail.MicrocoreWindow

namespace IsingBulk.Tail
noncomputable section
open Filter
open scoped Topology

theorem allBranchExterior_near_slope_choice (U b : ℝ) (hU : 0 ≤ U) (hb : 0 < b) (hb1 : b ≤ 1) :
    1 ≤ (1+2*U)/b ∧ U/Real.sqrt (b/4) ≤ (1+2*U)/b := by
  refine ⟨(one_le_div hb).mpr (by linarith),?_⟩
  have he : U/Real.sqrt (b/4)=2*U*(Real.sqrt b)⁻¹ := by
    rw [Real.sqrt_div hb.le]
    norm_num
    ring
  rw [he,div_eq_mul_inv]
  exact (mul_le_mul_of_nonneg_left (allBranchExterior_inv_sqrt_le_inv hb hb1) (by positivity)).trans
    (mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr hb.le))

theorem allBranchExterior_scale_geometry (A c U : ℝ) (hA : 0 ≤ A) (hc : 0 < c)
    (hc1 : c ≤ 1) (hU : 0 ≤ U) :
    ∃ B₀ : ℝ, 0 < B₀ ∧ ∀ B : ℝ, B₀ ≤ B → ∀ N : ℕ, 1 ≤ N →
      let b := allBranchMicroRadius A c N
      let ρ := allBranchEqualityRadius B N
      0 < b ∧ b ≤ 1 ∧ 0 < ρ ∧ 4*ρ ≤ 1 ∧ 2*ρ ≤ b/8 ∧
      1 ≤ (1+2*U)/b ∧ U/Real.sqrt (b/4) ≤ (1+2*U)/b ∧ ((1+2*U)/b)*(4*ρ) ≤ 1 := by
  let M := 1+2*U
  have hM : 0 < M := by dsimp [M]; positivity
  let B₀ := max 1 (max (allBranchScaleThreshold A c) (allBranchScaleThreshold A (c/M)))
  have hB₀ : 0 < B₀ := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) (le_max_left _ _)
  refine ⟨B₀,hB₀,?_⟩
  intro B hB N hN
  have hB₁ : allBranchScaleThreshold A c ≤ B := ((le_max_left _ _).trans (le_max_right _ _)).trans hB
  have hB₂ : allBranchScaleThreshold A (c/M) ≤ B := ((le_max_right _ _).trans (le_max_right _ _)).trans hB
  have hb : 0 < allBranchMicroRadius A c N := microcoreRadius_pos A c hc N hN
  have hb1 : allBranchMicroRadius A c N ≤ 1 := (microcoreRadius_le_prefactor A c hA hc.le N hN).trans hc1
  have hρ := Real.exp_pos (-B*(N:ℝ))
  have hscale := all_branch_scale_inclusion hc hB₁ hN
  have hstrong := all_branch_negative_scale_inclusion (div_pos hc hM) hB₂ hN
  have he : allBranchMicroRadius A (c/M) N=allBranchMicroRadius A c N/M := by
    unfold allBranchMicroRadius
    ring
  rw [he] at hstrong
  have hmul := mul_le_mul_of_nonneg_left hstrong (div_nonneg hM.le hb.le)
  have hcancel : (M/allBranchMicroRadius A c N)*(allBranchMicroRadius A c N/M/16)=1/16 := by field_simp
  rw [hcancel] at hmul
  have hslope := allBranchExterior_near_slope_choice U _ hU hb hb1
  refine ⟨hb,hb1,hρ,by linarith,hscale,hslope.1,hslope.2,?_⟩
  change (M/allBranchMicroRadius A c N)*(4*allBranchEqualityRadius B N) ≤ 1
  nlinarith

/-- A single radial threshold handles any fixed multiple of epsilon over
the whole intermediate particle window. -/
theorem allBranchExterior_window_epsilon_multiple (D A c K : ℝ) (hD : 0 ≤ D)
    (hA : 0 ≤ A) (hc : 0 < c) (hK : 0 < K) :
    ∀ᶠ H : ℝ in atTop, ∀ N : ℕ, 1 ≤ N → (N:ℝ) ≤ D*Real.sqrt H →
      K*Real.exp (-H) ≤ allBranchMicroRadius A c N := by
  filter_upwards [microcore_window_epsilon_le_radius D A (c/K) hD hA (div_pos hc hK)] with H hH
  intro N hN hwindow
  have hh := mul_le_mul_of_nonneg_left (hH N hN hwindow) hK.le
  have he : K*microcoreRadius A (c/K) N=allBranchMicroRadius A c N := by
    unfold microcoreRadius allBranchMicroRadius
    field_simp
  rwa [he] at hh

theorem allBranchExterior_source_degree {p N j : ℕ} (hp : 1 ≤ p)
    (hN : 2*p+2 ≤ N) (hj : j ≤ (2*p)^2/2-1) : 2*j+2 ≤ N*(N-1) := by
  have hsq : 2 ≤ (2*p)^2 := by nlinarith
  have hj' : 2*j+2 ≤ (2*p)^2 := by omega
  have hN1 : 1 ≤ N := by omega
  have hpred := Nat.sub_add_cancel hN1
  nlinarith

end
end IsingBulk.Tail
