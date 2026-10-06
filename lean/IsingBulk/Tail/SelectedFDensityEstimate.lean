import IsingBulk.Tail.SelectedFDiscountedWeights
import IsingBulk.Tail.SelectedFRootProduct
import IsingBulk.Tail.SelectorOriginal
import IsingBulk.Tail.ExteriorConvergenceBounds

/-! Exact canceled selected density estimate. Every inverse-product numerator,
global denominator, and vertex residue is retained before Gaussian discount. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First
open scoped BigOperators

theorem canceledReducedDensity_continued_eq {N : ℕ} (s : ℂ) (y : Fin N → ℂ)
    (hy : ∀ i, y i ≠ 0) (hW : ∀ i, sourceW s (y i) ∈ continuedRootDomain)
    (hygap : ∀ i j, 1-y i*y j ≠ 0) :
    canceledReducedDensity (fun i => selectedContinuedRoot s (y i)) y =
      reducedDensity (fun i => selectedContinuedRoot s (y i)) y := by
  unfold canceledReducedDensity reducedDensity selectedContinuedRoot
  rw [canceledPairProduct_eq s _ y hy
    (fun i => continuedRoot_nonzero _) (fun i => by
      have h := continuedRoot_quadratic (sourceW s (y i))
      dsimp [selectedContinuedRoot,sourceW,sourceS] at h ⊢
      linear_combination h)
    hygap (fun i j => continuedRoot_pair_gap (hW i) (hW j))]
  ring

theorem reducedDensity_discounted_bound {N : ℕ} (z y : Fin N → ℂ)
    (b η C eps : ℝ) (θ : Fin N → ℝ) {A B gZ gY a L : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hgZ : 0 < gZ) (hgY : 0 < gY) (ha : 0 < a) (hL : 0 < L)
    (hnum : ‖(coordinateProduct z)⁻¹+(coordinateProduct y)⁻¹‖ ≤ 2*A^N)
    (hZ : gZ ≤ ‖1-coordinateProduct z‖) (hY : gY ≤ ‖1-coordinateProduct y‖)
    (hp : ‖First.pairProduct z‖ ≤ B^N*Real.exp (-a*((selectedCompactIndexSet b η θ).card:ℝ)^2))
    (hv : ∀ i, ‖residueFactor (z i)‖ ≤ selectedOneBodyBound b η C eps (θ i)) :
    ‖reducedDensity z y‖ ≤
      (2*(A*B)^N/(gZ*gY))*Real.exp ((Real.log L)^2/(4*a))*
        ((∏ i, discountedSelectedWeight b η C eps L (θ i))*‖First.pairProduct y‖) := by
  have hden : gZ*gY ≤ ‖(1-coordinateProduct z)*(1-coordinateProduct y)‖ := by
    rw [norm_mul]
    exact mul_le_mul hZ hY hgY.le (norm_nonneg _)
  have hglob : ‖((coordinateProduct z)⁻¹+(coordinateProduct y)⁻¹)/
      ((1-coordinateProduct z)*(1-coordinateProduct y))‖ ≤ 2*A^N/(gZ*gY) := by
    rw [norm_div]
    exact div_le_div₀ (by positivity) hnum (mul_pos hgZ hgY) hden
  have hres : ∏ i, ‖residueFactor (z i)‖ ≤ ∏ i, selectedOneBodyBound b η C eps (θ i) :=
    Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hv i)
  have hd := gaussian_selected_weight_product b η C eps hC ha hL θ
  calc
    ‖reducedDensity z y‖ ≤ (2*A^N/(gZ*gY))*(B^N*Real.exp (-a*((selectedCompactIndexSet b η θ).card:ℝ)^2))*
        ‖First.pairProduct y‖*(∏ i, selectedOneBodyBound b η C eps (θ i)) := by
      simp only [reducedDensity,norm_mul,norm_prod]
      gcongr
    _ = (2*(A*B)^N/(gZ*gY))*
        (Real.exp (-a*((selectedCompactIndexSet b η θ).card:ℝ)^2)*(∏ i, selectedOneBodyBound b η C eps (θ i)))*
        ‖First.pairProduct y‖ := by rw [mul_pow]; ring
    _ ≤ (2*(A*B)^N/(gZ*gY))*
        (Real.exp ((Real.log L)^2/(4*a))*(∏ i, discountedSelectedWeight b η C eps L (θ i)))*
        ‖First.pairProduct y‖ := by gcongr
    _ = _ := by ring

/-- Literal factorial and angular normalization, with no discarded N-dependence. -/
theorem continuedPulledDensity_norm {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ)
    (s : ℂ) (θ : Fin N → ℝ) :
    ‖continuedPulledDensity f r τ lam s θ‖ =
      ((N.factorial:ℝ)⁻¹*(2*Real.pi)⁻¹^N)*
      ‖(angularJacobian f τ lam θ).det‖*(∏ i, ‖deformedPoint f r τ lam θ i‖)*
      ‖canceledReducedDensity (fun i => selectedContinuedRoot s (deformedPoint f r τ lam θ i))
        (deformedPoint f r τ lam θ)‖ := by
  simp only [continuedPulledDensity,norm_mul,norm_inv,Complex.norm_natCast,norm_prod,
    zpow_neg,zpow_natCast,norm_pow,Complex.norm_I,Complex.norm_ofNat,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,mul_one,inv_pow]


end
end IsingBulk.Tail
