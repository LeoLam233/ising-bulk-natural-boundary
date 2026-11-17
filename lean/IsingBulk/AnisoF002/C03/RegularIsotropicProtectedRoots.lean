import IsingBulk.AnisoF002.C03.RegularProtectedRoots
import IsingBulk.AnisoF002.C03.RegularIsotropicCompletePairBounds
import IsingBulk.AnisoF002.C03.RegularIsotropicMixedDenominators
import IsingBulk.AnisoF002.C03.RegularFilledMatchingBounds

/-!
# The actual mixed isotropic contour has one protected parameter disk

All constants are constructed from the original boundary geometry and
chosen deformation before N, the radial parameter and every angle.
The continuation starts at the actual physical roots and includes all
pair and product denominators on the full mixed support.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set
open scoped Topology BigOperators
open IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.RegularTail.C03

def mixedContinuedRoots {N : ℕ} (S : ℂ) (η τ : ℝ) (θ : Fin N → ℝ) (z : ℂ) : Fin N → ℂ :=
  continuedRoots (fun i => isotropicDispersion (S, actualHomotopyAngle η τ 1 θ i))
    (fun i => isotropicInteriorRoot (S, actualHomotopyAngle η τ 1 θ i)) z

structure ActualMixedRootControl (α b η τ δ : ℝ) where
  beta : ℝ
  pairConstant : ℝ
  pairGap : ℝ
  productGap : ℝ
  radius : ℝ
  beta_pos : 0 < beta
  pairConstant_ge_one : 1 ≤ pairConstant
  pairGap_pos : 0 < pairGap
  productGap_pos : 0 < productGap
  radius_pos : 0 < radius
  radius_le_one : radius ≤ 1
  center_pair : ∀ (N : ℕ), 0 < N → ∀ ε : ℝ, 0 < ε → ε ≤ δ →
    ∀ θ : Fin N → ℝ, ∀ i j,
      ‖canceledPair 1
        (isotropicInteriorRoot (isotropicRadialParameter α ε, actualHomotopyAngle η τ 1 θ i))
        (isotropicInteriorRoot (isotropicRadialParameter α ε, actualHomotopyAngle η τ 1 θ j))
        (Complex.exp (actualHomotopyAngle η τ 1 θ i * Complex.I))
        (Complex.exp (actualHomotopyAngle η τ 1 θ j * Complex.I))‖ ≤
      pairConstant * mixedVertexWeight (mixedCosBranchCoordinates b beta θ) i *
        mixedVertexWeight (mixedCosBranchCoordinates b beta θ) j
  center_gap : ∀ (N : ℕ), 0 < N → ∀ ε : ℝ, 0 < ε → ε ≤ δ →
    ∀ θ : Fin N → ℝ, 1 / 4 ≤ actualUpperPopulation η θ →
      1 / 4 ≤ actualLowerPopulation η θ → ∀ i j,
      pairGap / N ≤ ‖1 -
        isotropicInteriorRoot (isotropicRadialParameter α ε, actualHomotopyAngle η τ 1 θ i) *
        isotropicInteriorRoot (isotropicRadialParameter α ε, actualHomotopyAngle η τ 1 θ j)‖
  disk_bounds : ∀ (N : ℕ), 0 < N → ∀ ε : ℝ, 0 < ε → ε ≤ δ →
    ∀ θ : Fin N → ℝ, 1 / 4 ≤ actualUpperPopulation η θ →
      1 / 4 ≤ actualLowerPopulation η θ → ∀ z : ℂ, ‖z‖ ≤ radius / (N : ℝ) ^ 6 →
      (∀ i, AnalyticAt ℂ (fun t => mixedContinuedRoots (isotropicRadialParameter α ε) η τ θ t i) z) ∧
      (∀ i, ‖mixedContinuedRoots (isotropicRadialParameter α ε) η τ θ z i‖ ≤
        2 * ‖isotropicInteriorRoot (isotropicRadialParameter α ε, actualHomotopyAngle η τ 1 θ i)‖) ∧
      (∀ i j, ‖1 - isotropicInteriorRoot (isotropicRadialParameter α ε, actualHomotopyAngle η τ 1 θ i) *
          isotropicInteriorRoot (isotropicRadialParameter α ε, actualHomotopyAngle η τ 1 θ j)‖ / 2 ≤
        ‖1 - mixedContinuedRoots (isotropicRadialParameter α ε) η τ θ z i *
          mixedContinuedRoots (isotropicRadialParameter α ε) η τ θ z j‖) ∧
      (∀ i j, ‖schur (mixedContinuedRoots (isotropicRadialParameter α ε) η τ θ z i)
        (mixedContinuedRoots (isotropicRadialParameter α ε) η τ θ z j)‖ ≤ 1 + 1 / (N : ℝ) ^ 2) ∧
      ‖∏ i, mixedContinuedRoots (isotropicRadialParameter α ε) η τ θ z i‖ ≤ 1 - productGap / (2 * N)

theorem exists_actual_mixed_root_control (α b η : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) (hη : 0 < η)
    (hwidth : 4 * η ≤ Real.sin b) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ τ : ℝ, 0 < τ → τ ≤ δ →
      Nonempty (ActualMixedRootControl α b η τ δ) := by
  obtain ⟨β, δp, hβ, hδp, hδp1, hp⟩ :=
    exists_actual_complete_pair_weights α b η hα hb hpoint hη hwidth
  obtain ⟨δg, hδg, _, hg⟩ := exists_actual_mixed_pair_gap α b η hα hb hpoint hη hwidth
  let δ := min δp δg
  have hδ : 0 < δ := lt_min hδp hδg
  have hδp' : δ ≤ δp := min_le_left _ _
  have hδg' : δ ≤ δg := min_le_right _ _
  have hδ1 : δ ≤ 1 := hδp'.trans hδp1
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro τ hτ hτδ
  obtain ⟨C, hC, hCbound⟩ := hp τ hτ (hτδ.trans hδp')
  obtain ⟨c, hc, hcBound⟩ := hg τ hτ (hτδ.trans hδg')
  let glog := mixedRootAttenuationConstant * η * τ / 8
  have hglog : 0 < glog := by dsimp [glog]; positivity [mixedRootAttenuationConstant_pos]
  let g := glog / (1 + glog)
  have hgpos : 0 < g := by dsimp [g]; positivity
  obtain ⟨ρ, hρ, hρ1, hprotected⟩ := exists_uniform_reciprocal_root_disk
    (3 + Real.exp 1) isotropicRootNormFloor c g (by positivity)
    isotropicRootNormFloor_pos hc hgpos
  refine ⟨⟨β, C, c, g, ρ, hβ, hC, hc, hgpos, hρ, hρ1, ?_, ?_, ?_⟩⟩
  · intro N hN ε hε hεδ θ i j
    exact hCbound N hN ε hε (hεδ.trans hδp') θ i j
  · intro N hN ε hε hεδ θ hP hQ i j
    exact hcBound N hN ε hε (hεδ.trans hδg') θ hP hQ i j
  · intro N hN ε hε hεδ θ hP hQ z hz
    let S := isotropicRadialParameter α ε
    let W : Fin N → ℂ := fun i => isotropicDispersion (S, actualHomotopyAngle η τ 1 θ i)
    let r : Fin N → ℂ := fun i => isotropicInteriorRoot (S, actualHomotopyAngle η τ 1 θ i)
    have hSi : 0 < S.im := (isotropicRadialParameter_estimates α ε hα hε (hεδ.trans hδ1)).2.2.2.1
    have hSn : ‖S‖ ≤ 3 := isotropicRadialParameter_norm_le_three α ε hε.le (hεδ.trans hδ1)
    have hτ1 : τ ≤ 1 := hτδ.trans hδ1
    have hWi (i : Fin N) : 0 < (W i).im :=
      actual_balanced_homotopy_sheet S hSi η τ 1 hη hτ.le zero_le_one θ i
    have hri (i : Fin N) : ‖r i‖ ≤ 1 := upperEdgeRoot_norm_le_one (Or.inl (hWi i))
    have hrprod : ‖∏ i, r i‖ ≤ 1 - g / N := by
      have hh := one_sub_norm_of_log_gap
        (Finset.prod_ne_zero_iff.mpr (fun i _ => isotropicInteriorRoot_ne_zero _)) hglog hN
        (actual_mixed_product_log_gap hN S hSi hSn hη ⟨hτ.le, hτ1⟩ θ hP hQ)
      have he : glog / ((1 + glog) * (N : ℝ)) = g / N := (div_div glog (1 + glog) (N : ℝ)).symm
      rw [he] at hh
      linarith
    exact hprotected N hN W r
      (fun i => isotropicInteriorRoot_polynomial (S, actualHomotopyAngle η τ 1 θ i))
      (fun i => actual_balanced_dispersion_norm_bound hN S hSn η ⟨hτ.le, hτ1⟩ θ i)
      (fun i => actual_balanced_root_norm_floor hN S hSi hSn hη ⟨hτ.le, hτ1⟩ θ i) hri
      (fun i j => hcBound N hN ε hε (hεδ.trans hδg') θ hP hQ i j)
      (fun i j => schur_norm_le_one_closed_lower _ _ (hri i) (hri j)
        (upperEdgeRoot_im_neg (Or.inl (hWi i))).le (upperEdgeRoot_im_neg (Or.inl (hWi j))).le)
      hrprod z hz

end
end IsingBulk.AnisoF002.Isotropic
