import IsingBulk.HT.Contour.SignedContinuation
import IsingBulk.Tail.SelectedFDensityEstimate

/-! Quantitative signed density transfer. The inverse-product numerator,
all paired factors and all one-body residues are retained explicitly. -/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Tail
open scoped BigOperators

def signedReducedDensity {N : ℕ} (σ : ℂ) (z y : Fin N → ℂ) : ℂ :=
  signedGlobalFactor σ (coordinateProduct z) (coordinateProduct y)*
    First.pairProduct z*First.pairProduct y*∏ i,residueFactor (z i)

theorem signed_canceledReducedDensity_continued_eq (σ : ℂ) {N : ℕ} (s : ℂ) (y : Fin N → ℂ)
    (hy : ∀ i, y i ≠ 0) (hW : ∀ i, sourceW s (y i) ∈ continuedRootDomain)
    (hygap : ∀ i j, 1-y i*y j ≠ 0) :
    signedCanceledDensity σ (fun i => selectedContinuedRoot s (y i)) y =
      signedReducedDensity σ (fun i => selectedContinuedRoot s (y i)) y := by
  unfold signedCanceledDensity signedReducedDensity signedGlobalFactor selectedContinuedRoot
  rw [canceledPairProduct_eq s _ y hy
    (fun i => continuedRoot_nonzero _) (fun i => by
      have h := continuedRoot_quadratic (sourceW s (y i))
      dsimp [selectedContinuedRoot,sourceW,sourceS] at h ⊢
      linear_combination h)
    hygap (fun i j => continuedRoot_pair_gap (hW i) (hW j))]
  ring

theorem signed_reducedDensity_discounted_bound (σ : ℂ) {N : ℕ} (z y : Fin N → ℂ)
    (b η C eps : ℝ) (θ : Fin N → ℝ) {A B gZ gY a L : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hgZ : 0 < gZ) (hgY : 0 < gY) (ha : 0 < a) (hL : 0 < L)
    (hnum : ‖(coordinateProduct z)⁻¹+(coordinateProduct y)⁻¹‖ ≤ 2*A^N)
    (hZ : gZ ≤ ‖1-σ*coordinateProduct z‖) (hY : gY ≤ ‖1-σ*coordinateProduct y‖)
    (hp : ‖First.pairProduct z‖ ≤ B^N*Real.exp (-a*((selectedCompactIndexSet b η θ).card:ℝ)^2))
    (hv : ∀ i, ‖residueFactor (z i)‖ ≤ selectedOneBodyBound b η C eps (θ i)) :
    ‖signedReducedDensity σ z y‖ ≤
      (2*(A*B)^N/(gZ*gY))*Real.exp ((Real.log L)^2/(4*a))*
        ((∏ i, discountedSelectedWeight b η C eps L (θ i))*‖First.pairProduct y‖) := by
  have hden : gZ*gY ≤ ‖(1-σ*coordinateProduct z)*(1-σ*coordinateProduct y)‖ := by
    rw [norm_mul]
    exact mul_le_mul hZ hY hgY.le (norm_nonneg _)
  have hglob : ‖((coordinateProduct z)⁻¹+(coordinateProduct y)⁻¹)/
      ((1-σ*coordinateProduct z)*(1-σ*coordinateProduct y))‖ ≤ 2*A^N/(gZ*gY) := by
    rw [norm_div]
    exact div_le_div₀ (by positivity) hnum (mul_pos hgZ hgY) hden
  have hres : ∏ i, ‖residueFactor (z i)‖ ≤ ∏ i, selectedOneBodyBound b η C eps (θ i) :=
    Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hv i)
  have hd := gaussian_selected_weight_product b η C eps hC ha hL θ
  calc
    ‖signedReducedDensity σ z y‖ ≤ (2*A^N/(gZ*gY))*(B^N*Real.exp (-a*((selectedCompactIndexSet b η θ).card:ℝ)^2))*
        ‖First.pairProduct y‖*(∏ i, selectedOneBodyBound b η C eps (θ i)) := by
      simp only [signedReducedDensity,signedGlobalFactor,norm_mul,norm_prod]
      gcongr
    _ = (2*(A*B)^N/(gZ*gY))*
        (Real.exp (-a*((selectedCompactIndexSet b η θ).card:ℝ)^2)*(∏ i, selectedOneBodyBound b η C eps (θ i)))*
        ‖First.pairProduct y‖ := by rw [mul_pow]; ring
    _ ≤ (2*(A*B)^N/(gZ*gY))*
        (Real.exp ((Real.log L)^2/(4*a))*(∏ i, discountedSelectedWeight b η C eps L (θ i)))*
        ‖First.pairProduct y‖ := by gcongr
    _ = _ := by ring

/-- Literal factorial and angular normalization, with no discarded N-dependence. -/
theorem signed_continuedPulledDensity_norm (σ : ℂ) {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ)
    (s : ℂ) (θ : Fin N → ℝ) :
    ‖signedContinuedPulledDensity σ f r τ lam s θ‖ =
      ((N.factorial:ℝ)⁻¹*(2*Real.pi)⁻¹^N)*
      ‖(angularJacobian f τ lam θ).det‖*(∏ i, ‖deformedPoint f r τ lam θ i‖)*
      ‖signedCanceledDensity σ (fun i => selectedContinuedRoot s (deformedPoint f r τ lam θ i))
        (deformedPoint f r τ lam θ)‖ := by
  simp only [signedContinuedPulledDensity,norm_mul,norm_inv,Complex.norm_natCast,norm_prod,
    zpow_neg,zpow_natCast,norm_pow,Complex.norm_I,Complex.norm_ofNat,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,mul_one,inv_pow]


end
end IsingBulk.HT.Contour
