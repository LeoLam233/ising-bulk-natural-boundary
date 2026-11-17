import IsingBulk.AnisoF002.C03.RegularIsotropicOppositePairs

/-!
# Constructed weighted bounds for every actual complete pair

All angular tuples are included. Same-side pairs contract, pairs with
an away coordinate have a compact gap, and only opposite true branches
pay the actual population weight. Constants precede every particle.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set
open scoped Topology BigOperators Classical
open IsingBulk.AnisoF002.RegularTail

theorem canceledPair_swap (B r s y v : ℂ) :
    canceledPair B r s y v = canceledPair B s r v y := by
  unfold canceledPair
  congr 1 <;> ring

theorem actual_complete_pair_weighted_of_geometry {N : ℕ} (hN : 0 < N)
    (S : ℂ) (hSi : 0 < S.im) (hSn : ‖S‖ ≤ 3) (b η β τ d C : ℝ)
    (hη : 0 < η) (hwidth : 4 * η ≤ Real.sin b) (hβ : β ≤ (Real.sin b) ^ 2 / 8)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hd : 0 < d) (hC : 1 ≤ C)
    (hCaway : 4 * Real.exp 1 ^ 2 / d ^ 2 ≤ C)
    (hCop : 32 * Real.exp 1 ^ 2 / (isotropicRootNormFloor * η * τ) ≤ C)
    (θ : Fin N → ℝ)
    (hnear : ∀ i, i ∈ mixedCosBranchCoordinates b β θ →
      ‖1 - isotropicInteriorRoot (S, actualHomotopyAngle η τ 1 θ i)‖ ≤ 1 / 4)
    (haway : ∀ i j, (i ∉ mixedCosBranchCoordinates b β θ ∨ j ∉ mixedCosBranchCoordinates b β θ) →
      d ≤ ‖1 - isotropicInteriorRoot (S, actualHomotopyAngle η τ 1 θ i) *
        isotropicInteriorRoot (S, actualHomotopyAngle η τ 1 θ j)‖)
    (i j : Fin N) :
    ‖canceledPair 1 (isotropicInteriorRoot (S, actualHomotopyAngle η τ 1 θ i))
      (isotropicInteriorRoot (S, actualHomotopyAngle η τ 1 θ j))
      (Complex.exp (actualHomotopyAngle η τ 1 θ i * Complex.I))
      (Complex.exp (actualHomotopyAngle η τ 1 θ j * Complex.I))‖ ≤
        C * mixedVertexWeight (mixedCosBranchCoordinates b β θ) i *
          mixedVertexWeight (mixedCosBranchCoordinates b β θ) j := by
  let v := mixedVertexWeight (mixedCosBranchCoordinates b β θ)
  have hvi : 1 ≤ v i := mixedVertexWeight_ge_one _ i
  have hvj : 1 ≤ v j := mixedVertexWeight_ge_one _ j
  have hvi0 : 0 ≤ v i := zero_le_one.trans hvi
  have hvj0 : 0 ≤ v j := zero_le_one.trans hvj
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hCprod : C ≤ C * v i * v j := by
    have h1 : C ≤ C * v i := by nlinarith
    have h2 : C * v i ≤ C * v i * v j := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hvj (mul_nonneg hC0 hvi0)
    exact h1.trans h2
  have h1prod : 1 ≤ C * v i * v j := hC.trans hCprod
  have hfar (hij : i ∉ mixedCosBranchCoordinates b β θ ∨ j ∉ mixedCosBranchCoordinates b β θ) :
      ‖canceledPair 1 (isotropicInteriorRoot (S, actualHomotopyAngle η τ 1 θ i))
        (isotropicInteriorRoot (S, actualHomotopyAngle η τ 1 θ j))
        (Complex.exp (actualHomotopyAngle η τ 1 θ i * Complex.I))
        (Complex.exp (actualHomotopyAngle η τ 1 θ j * Complex.I))‖ ≤ C * v i * v j := by
    have hb := canceledPair_norm_bound_by_gap
      (upperEdgeRoot_norm_le_one (Or.inl (actual_balanced_homotopy_sheet S hSi η τ 1 hη hτ.le zero_le_one θ i)))
      (upperEdgeRoot_norm_le_one (Or.inl (actual_balanced_homotopy_sheet S hSi η τ 1 hη hτ.le zero_le_one θ j)))
      ((actualHomotopyAngle_im_abs_le hN η τ hτ.le θ i).trans hτ1)
      ((actualHomotopyAngle_im_abs_le hN η τ hτ.le θ j).trans hτ1)
    have hsq := pow_le_pow_left₀ hd.le (haway i j hij) 2
    exact hb.trans ((div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hd) hsq).trans
      (hCaway.trans hCprod))
  by_cases hi : i ∈ mixedCosBranchCoordinates b β θ
  · by_cases hj : j ∈ mixedCosBranchCoordinates b β θ
    · rcases cosine_band_bump_plateau b η (θ i) β hη hwidth hβ (Finset.mem_filter.mp hi).2
        with ⟨hpi, hmi⟩ | ⟨hpi, hmi⟩
      · rcases cosine_band_bump_plateau b η (θ j) β hη hwidth hβ (Finset.mem_filter.mp hj).2
          with ⟨hpj, hmj⟩ | ⟨hpj, hmj⟩
        · exact (actual_balanced_same_side_pair hN S hSi η τ hη hτ.le θ i j
            (Or.inl ⟨(upperPeriodicBump_one_sin_pos hη hpi).le,
              (upperPeriodicBump_one_sin_pos hη hpj).le⟩)).trans h1prod
        · have hb := actual_opposite_branch_pair_weighted hN S hSi hSn b η β τ
            hη hwidth hβ hτ hτ1 θ i j hi hj hpi hmi hpj hmj (hnear i hi) (hnear j hj)
          exact hb.trans (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hCop hvi0) hvj0)
      · rcases cosine_band_bump_plateau b η (θ j) β hη hwidth hβ (Finset.mem_filter.mp hj).2
          with ⟨hpj, hmj⟩ | ⟨hpj, hmj⟩
        · have hb := actual_opposite_branch_pair_weighted hN S hSi hSn b η β τ
            hη hwidth hβ hτ hτ1 θ j i hj hi hpj hmj hpi hmi (hnear j hj) (hnear i hi)
          rw [canceledPair_swap (1 : ℂ)
            (isotropicInteriorRoot (S, actualHomotopyAngle η τ 1 θ j))
            (isotropicInteriorRoot (S, actualHomotopyAngle η τ 1 θ i))] at hb
          have hh := hb.trans (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hCop hvj0) hvi0)
          convert hh using 1
          ring
        · exact (actual_balanced_same_side_pair hN S hSi η τ hη hτ.le θ i j
            (Or.inr ⟨(lowerPeriodicBump_one_sin_neg hη hmi).le,
              (lowerPeriodicBump_one_sin_neg hη hmj).le⟩)).trans h1prod
    · exact hfar (Or.inr hj)
  · exact hfar (Or.inl hi)

theorem exists_actual_complete_pair_weights (α b η : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) (hη : 0 < η)
    (hwidth : 4 * η ≤ Real.sin b) :
    ∃ β δ : ℝ, 0 < β ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ τ : ℝ, 0 < τ → τ ≤ δ → ∃ C : ℝ, 1 ≤ C ∧
        ∀ (N : ℕ), 0 < N → ∀ ε : ℝ, 0 < ε → ε ≤ δ →
        ∀ θ : Fin N → ℝ, ∀ i j,
          ‖canceledPair 1
            (isotropicInteriorRoot (isotropicRadialParameter α ε, actualHomotopyAngle η τ 1 θ i))
            (isotropicInteriorRoot (isotropicRadialParameter α ε, actualHomotopyAngle η τ 1 θ j))
            (Complex.exp (actualHomotopyAngle η τ 1 θ i * Complex.I))
            (Complex.exp (actualHomotopyAngle η τ 1 θ j * Complex.I))‖ ≤
            C * mixedVertexWeight (mixedCosBranchCoordinates b β θ) i *
              mixedVertexWeight (mixedCosBranchCoordinates b β θ) j := by
  obtain ⟨β, δ, d, hβ, hβsin, hδ, hδ1, hd, hgeom⟩ :=
    exists_actual_mixed_root_geometry α b η hα hb hpoint hη
  refine ⟨β, δ, hβ, hδ, hδ1, ?_⟩
  intro τ hτ hτδ
  let C := max 1 (max (4 * Real.exp 1 ^ 2 / d ^ 2)
    (32 * Real.exp 1 ^ 2 / (isotropicRootNormFloor * η * τ)))
  refine ⟨C, le_max_left _ _, ?_⟩
  intro N hN ε hε hεδ θ i j
  obtain ⟨hnear, haway⟩ := hgeom N hN ε hε hεδ τ ⟨hτ.le, hτδ⟩ θ
  apply actual_complete_pair_weighted_of_geometry hN (isotropicRadialParameter α ε)
    (isotropicRadialParameter_estimates α ε hα hε (hεδ.trans hδ1)).2.2.2.1
    (isotropicRadialParameter_norm_le_three α ε hε.le (hεδ.trans hδ1))
    b η β τ d C hη hwidth hβsin hτ (hτδ.trans hδ1) hd (le_max_left _ _)
    ((le_max_left _ _).trans (le_max_right _ _)) ((le_max_right _ _).trans (le_max_right _ _)) θ
  · intro k hk
    exact hnear k (Finset.mem_filter.mp hk).2
  · intro k l hkl
    apply haway k l
    rcases hkl with hk | hl
    · left
      have hnot : ¬ |Real.cos (θ k) - Real.cos b| ≤ β := by
        intro h
        exact hk (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      exact lt_of_not_ge hnot
    · right
      have hnot : ¬ |Real.cos (θ l) - Real.cos b| ≤ β := by
        intro h
        exact hl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      exact lt_of_not_ge hnot

end
end IsingBulk.AnisoF002.Isotropic
