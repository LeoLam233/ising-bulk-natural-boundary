import IsingBulk.AnisoF002.C03.RegularIsotropicMixedGeometry

/-!
# A fixed product gap from the actual compact exterior anchor

A single genuine exterior root supplies the full product denominator
gap. The angular anchor is kept explicit; all other physical roots
remain in the product and require only their proved norm bound.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set
open scoped Topology BigOperators
open IsingBulk.AnisoF002.RegularTail

def isotropicRootNormFloor : ℝ := 1 / (2 * (3 + Real.exp 1) + 1)

theorem isotropicRootNormFloor_pos : 0 < isotropicRootNormFloor := by
  unfold isotropicRootNormFloor
  positivity

theorem reciprocal_root_real_part_bound {W r : ℂ}
    (hp : r ^ 2 - 2 * W * r + 1 = 0) (hr : r ≠ 0) :
    2 * W.re ≤ ‖r‖ + ‖r‖⁻¹ := by
  have he : 2 * W = r + r⁻¹ := by
    apply mul_right_cancel₀ hr
    field_simp
    linear_combination -hp
  have hre := congrArg Complex.re he
  simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul,
    sub_zero, Complex.add_re] at hre
  have h1 := Complex.re_le_norm r
  have h2 := Complex.re_le_norm r⁻¹
  rw [norm_inv] at h2
  linarith

theorem upperEdgeRoot_exterior_gap {W : ℂ} (hW : 0 < W.im)
    {H c : ℝ} (hH : 0 ≤ H) (hWH : ‖W‖ ≤ H) (hc : 0 ≤ c) (hRe : 1 + c ≤ W.re) :
    2 * c / (2 * H + 1) ≤ 1 - ‖upperEdgeRoot W‖ := by
  let t := ‖upperEdgeRoot W‖
  have ht : 0 < t := norm_pos_iff.mpr (upperEdgeRoot_ne_zero W)
  have ht1 : t ≤ 1 := (upperEdgeRoot_norm_lt_one hW).le
  have hlo : 1 / (2 * H + 1) ≤ t := upperEdgeRoot_norm_lower hW hH hWH
  have hre := reciprocal_root_real_part_bound (upperEdgeRoot_polynomial W) (upperEdgeRoot_ne_zero W)
  change 2 * W.re ≤ t + t⁻¹ at hre
  have hm := mul_le_mul_of_nonneg_right hre ht.le
  have he : (t + t⁻¹) * t = t ^ 2 + 1 := by rw [add_mul, inv_mul_cancel₀ ht.ne', pow_two]
  rw [he] at hm
  have hcW := mul_le_mul_of_nonneg_right hRe ht.le
  have hcl := mul_le_mul_of_nonneg_left hlo (show 0 ≤ 2 * c by positivity)
  change 2 * c / (2 * H + 1) ≤ 1 - t
  have hec : 2 * c * (1 / (2 * H + 1)) = 2 * c / (2 * H + 1) := by ring
  rw [hec] at hcl
  nlinarith

theorem actual_balanced_root_norm_floor {N : ℕ} (hN : 0 < N)
    (S : ℂ) (hSi : 0 < S.im) (hSn : ‖S‖ ≤ 3) {η τ : ℝ}
    (hη : 0 < η) (hτ : τ ∈ Icc 0 1) (θ : Fin N → ℝ) (i : Fin N) :
    isotropicRootNormFloor ≤ ‖isotropicInteriorRoot (S, actualHomotopyAngle η τ 1 θ i)‖ :=
  upperEdgeRoot_norm_lower (actual_balanced_homotopy_sheet S hSi η τ 1 hη hτ.1 zero_le_one θ i)
    (by positivity : 0 ≤ 3 + Real.exp 1) (actual_balanced_dispersion_norm_bound hN S hSn η hτ θ i)

def exteriorAnchorRootBound (c : ℝ) : ℝ := max (1 / 2) (1 - c * isotropicRootNormFloor)

theorem exteriorAnchorRootBound_spec {c : ℝ} (hc : 0 < c) :
    0 < exteriorAnchorRootBound c ∧ exteriorAnchorRootBound c < 1 := by
  constructor
  · exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (le_max_left _ _)
  · apply max_lt (by norm_num)
    have hh := mul_pos hc isotropicRootNormFloor_pos
    linarith

theorem actual_exterior_anchor_root_bound {N : ℕ} (hN : 0 < N)
    (α b ε η τ c : ℝ) (hα : 0 < α ∧ α < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hη : 0 < η) (hτ : τ ∈ Icc 0 1)
    (hc : 0 < c) (hsmall : 4 * ε + 2 * τ ≤ c / 2)
    (θ : Fin N → ℝ) (a : Fin N) (ha : c ≤ Real.cos b - Real.cos (θ a)) :
    ‖isotropicInteriorRoot (isotropicRadialParameter α ε, actualHomotopyAngle η τ 1 θ a)‖ ≤
      exteriorAnchorRootBound c := by
  let W := isotropicDispersion (isotropicRadialParameter α ε, actualHomotopyAngle η τ 1 θ a)
  have hpert := actual_balanced_dispersion_perturbation hN α ε η τ hα hε hε1 hτ θ a
  have hre := Complex.abs_re_le_norm
    (W - ((2 * Real.cos α - Real.cos (θ a) : ℝ) : ℂ))
  simp only [Complex.sub_re, Complex.ofReal_re] at hre
  have hRe : 1 + c / 2 ≤ W.re := by
    have he := (abs_le.mp (hre.trans (hpert.trans hsmall))).1
    linarith
  have hSi := (isotropicRadialParameter_estimates α ε hα hε hε1).2.2.2.1
  have hW : 0 < W.im := actual_balanced_homotopy_sheet _ hSi η τ 1 hη hτ.1 zero_le_one θ a
  have hWH : ‖W‖ ≤ 3 + Real.exp 1 := actual_balanced_dispersion_norm_bound hN _
    (isotropicRadialParameter_norm_le_three α ε hε.le hε1) η hτ θ a
  have hgap := upperEdgeRoot_exterior_gap hW (by positivity : 0 ≤ 3 + Real.exp 1)
    hWH (by positivity : 0 ≤ c / 2) hRe
  have he : 2 * (c / 2) / (2 * (3 + Real.exp 1) + 1) = c * isotropicRootNormFloor := by
    dsimp [isotropicRootNormFloor]
    ring
  rw [he] at hgap
  apply le_trans _ (le_max_right _ _)
  change ‖upperEdgeRoot W‖ ≤ 1 - c * isotropicRootNormFloor
  linarith

theorem product_norm_le_named_factor {N : ℕ} (r : Fin N → ℂ)
    (hr : ∀ i, ‖r i‖ ≤ 1) (a : Fin N) : ‖∏ i, r i‖ ≤ ‖r a‖ := by
  rw [norm_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ a)]
  have hp : (∏ i ∈ Finset.univ.erase a, ‖r i‖) ≤ 1 :=
    Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => hr i)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (norm_nonneg (r a))

theorem actual_exterior_anchor_product_bound {N : ℕ} (hN : 0 < N)
    (α b ε η τ c : ℝ) (hα : 0 < α ∧ α < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hη : 0 < η) (hτ : τ ∈ Icc 0 1)
    (hc : 0 < c) (hsmall : 4 * ε + 2 * τ ≤ c / 2)
    (θ : Fin N → ℝ) (a : Fin N) (ha : c ≤ Real.cos b - Real.cos (θ a)) :
    ‖actualBalancedRootProduct (isotropicRadialParameter α ε) η τ θ‖ ≤ exteriorAnchorRootBound c := by
  have hSi := (isotropicRadialParameter_estimates α ε hα hε hε1).2.2.2.1
  apply (product_norm_le_named_factor _ (fun i =>
    (upperEdgeRoot_norm_lt_one (actual_balanced_homotopy_sheet _ hSi η τ 1 hη hτ.1 zero_le_one θ i)).le) a).trans
  exact actual_exterior_anchor_root_bound hN α b ε η τ c hα hpoint hε hε1 hη hτ hc hsmall θ a ha

end
end IsingBulk.AnisoF002.Isotropic
