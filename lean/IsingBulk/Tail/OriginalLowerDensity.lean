import IsingBulk.Tail.OriginalCompletePairProduct
import IsingBulk.Tail.OriginalResidueL1
import IsingBulk.Tail.OriginalDiskGlobalFactors
import IsingBulk.Tail.ExteriorConvergenceBounds
import IsingBulk.Tail.SelectorOriginal
import IsingBulk.Tail.OriginalDensityMajorant

/-! Literal original K density with complete-pair suppression, exact
normalization, and both square-root residue arcs retained. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set MeasureTheory
open scoped BigOperators

theorem original_pulledDensity_norm {N : ℕ} (f : SelectorFunctions) {r : ℝ} (hr : 0≤r)
    (τ : ℝ) (s : ℂ) (θ : Fin N → ℝ) :
    ‖pulledDensity f r τ 0 s θ‖ = (N.factorial:ℝ)⁻¹*(r/(2*Real.pi))^N*
      ‖canceledReducedDensity (fun i => globalRoot s (anglePoint r (θ i))) (angleTuple r θ)‖ := by
  unfold pulledDensity
  rw [deformedPoint_zero,angularJacobian_zero,Matrix.det_diagonal]
  simp only [norm_mul,norm_inv,Complex.norm_natCast,zpow_neg,zpow_natCast,norm_pow,
    Complex.norm_I,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos Real.pi_pos,mul_one,norm_prod,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    angleTuple,anglePoint_norm hr,one_pow]
  rw [div_pow]
  ring

theorem constructed_original_weight_norm_le {N : ℕ} (b η α : ℝ) (θ : Fin N → ℝ) :
    ‖(angularSelector (constructedSelector b η α) θ:ℂ)‖ ≤ 1 := by
  have h0 : 0 ≤ angularSelector (constructedSelector b η α) θ := by
    unfold angularSelector selectorWeight constructedSelector periodicUpperA
    exact Finset.prod_nonneg (fun i _ => sub_nonneg.mpr (thresholdStep_range _ _ _).2)
  have h1 : angularSelector (constructedSelector b η α) θ ≤ 1 := by
    unfold angularSelector selectorWeight constructedSelector periodicUpperA
    exact Finset.prod_le_one₀ (fun i _ => sub_nonneg.mpr (thresholdStep_range _ _ _).2)
      (fun i _ => sub_le_self _ (thresholdStep_range _ _ _).1)
  simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg h0] using h1

theorem original_canceled_density_complete_bound {N : ℕ} (hN : 2 ≤ N) {r A P κ : ℝ}
    (hr : 0<r) (hr1 : r<1) (hA : 0≤A) (_hP : 0≤P)
    (z y : Fin N → ℂ) (hz : ∀ i, ‖z i‖≤r) (hy : ∀ i, ‖y i‖=r)
    (hi : ∀ i, ‖(z i)⁻¹‖≤A)
    (hpair : ‖canceledPairProduct z y‖≤P^N*Real.exp (-κ*(N:ℝ)^2)) :
    ‖canceledReducedDensity z y‖ ≤
      (2*(max A r⁻¹*P)^N/(1-r^2)^2)*Real.exp (-κ*(N:ℝ)^2)*
        ∏ i, ‖residueFactor (z i)‖ := by
  have hg : 0<1-r^2 := by nlinarith
  have hnum := inverse_global_numerator_norm_le hA (inv_nonneg.mpr hr.le) hi
    (fun i => show ‖(y i)⁻¹‖ ≤ r⁻¹ by rw [norm_inv,hy i])
  have hdz := coordinateProduct_gap hN hr.le hr1 hz
  have hdy := coordinateProduct_gap hN hr.le hr1 (fun i => (hy i).le)
  have hden : (1-r^2)^2 ≤ ‖(1-coordinateProduct z)*(1-coordinateProduct y)‖ := by
    rw [norm_mul,pow_two]
    exact mul_le_mul hdz hdy hg.le (norm_nonneg _)
  have hglob : ‖((coordinateProduct z)⁻¹+(coordinateProduct y)⁻¹)/
      ((1-coordinateProduct z)*(1-coordinateProduct y))‖ ≤ 2*(max A r⁻¹)^N/(1-r^2)^2 := by
    rw [norm_div]
    exact div_le_div₀ (by positivity) hnum (sq_pos_of_pos hg) hden
  calc
    _ ≤ (2*(max A r⁻¹)^N/(1-r^2)^2)*(P^N*Real.exp (-κ*(N:ℝ)^2))*
        ∏ i, ‖residueFactor (z i)‖ := by
      simp only [canceledReducedDensity,norm_mul,norm_prod]
      gcongr
    _ = _ := by rw [mul_pow]; ring

end
end IsingBulk.Tail
