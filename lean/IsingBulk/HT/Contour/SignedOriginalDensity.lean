import IsingBulk.HT.Contour.SignedContinuation
import IsingBulk.Tail.OriginalCompletePairProduct
import IsingBulk.Tail.OriginalResidueL1
import IsingBulk.Tail.OriginalDiskGlobalFactors
import IsingBulk.Tail.ExteriorConvergenceBounds
import IsingBulk.Tail.SelectorOriginal
import IsingBulk.Tail.OriginalDensityMajorant

/-! Literal original K density with complete-pair suppression, exact
normalization, and both square-root residue arcs retained. -/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.Branch Set MeasureTheory
open scoped BigOperators

theorem signed_original_pulledDensity_norm (σ : ℂ) {N : ℕ} (f : SelectorFunctions) {r : ℝ} (hr : 0≤r)
    (τ : ℝ) (s : ℂ) (θ : Fin N → ℝ) :
    ‖signedPulledDensity σ f r τ 0 s θ‖ = (N.factorial:ℝ)⁻¹*(r/(2*Real.pi))^N*
      ‖signedCanceledDensity σ (fun i => globalRoot s (anglePoint r (θ i))) (angleTuple r θ)‖ := by
  unfold signedPulledDensity
  rw [deformedPoint_zero,angularJacobian_zero,Matrix.det_diagonal]
  simp only [norm_mul,norm_inv,Complex.norm_natCast,zpow_neg,zpow_natCast,norm_pow,
    Complex.norm_I,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos Real.pi_pos,mul_one,norm_prod,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    angleTuple,anglePoint_norm hr,one_pow]
  rw [div_pow]
  ring

theorem signed_coordinateProduct_gap (σ : ℂ) (hσ : ‖σ‖ = 1)
    {N : ℕ} (hN : 2 ≤ N) {z : Fin N → ℂ} {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hz : ∀ i, ‖z i‖ ≤ q) :
    1-q^2 ≤ ‖1-σ*coordinateProduct z‖ := by
  have hp : ‖coordinateProduct z‖ ≤ q^N := by
    simp only [coordinateProduct,norm_prod]
    calc
      ∏ i, ‖z i‖ ≤ ∏ _i : Fin N, q :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hz i)
      _ = q^N := by simp
  have he := pow_le_pow_of_le_one hq0 hq1.le hN
  have hn := signed_gap_lower σ (coordinateProduct z) hσ
  linarith

theorem signed_original_canceled_density_complete_bound (σ : ℂ) (hσ : ‖σ‖ = 1) {N : ℕ} (hN : 2 ≤ N) {r A P κ : ℝ}
    (hr : 0<r) (hr1 : r<1) (hA : 0≤A) (_hP : 0≤P)
    (z y : Fin N → ℂ) (hz : ∀ i, ‖z i‖≤r) (hy : ∀ i, ‖y i‖=r)
    (hi : ∀ i, ‖(z i)⁻¹‖≤A)
    (hpair : ‖canceledPairProduct z y‖≤P^N*Real.exp (-κ*(N:ℝ)^2)) :
    ‖signedCanceledDensity σ z y‖ ≤
      (2*(max A r⁻¹*P)^N/(1-r^2)^2)*Real.exp (-κ*(N:ℝ)^2)*
        ∏ i, ‖residueFactor (z i)‖ := by
  have hg : 0<1-r^2 := by nlinarith
  have hnum := inverse_global_numerator_norm_le hA (inv_nonneg.mpr hr.le) hi
    (fun i => show ‖(y i)⁻¹‖ ≤ r⁻¹ by rw [norm_inv,hy i])
  have hdz := signed_coordinateProduct_gap σ hσ hN hr.le hr1 hz
  have hdy := signed_coordinateProduct_gap σ hσ hN hr.le hr1 (fun i => (hy i).le)
  have hden : (1-r^2)^2 ≤ ‖(1-σ*coordinateProduct z)*(1-σ*coordinateProduct y)‖ := by
    rw [norm_mul,pow_two]
    exact mul_le_mul hdz hdy hg.le (norm_nonneg _)
  have hglob : ‖((coordinateProduct z)⁻¹+(coordinateProduct y)⁻¹)/
      ((1-σ*coordinateProduct z)*(1-σ*coordinateProduct y))‖ ≤ 2*(max A r⁻¹)^N/(1-r^2)^2 := by
    rw [norm_div]
    exact div_le_div₀ (by positivity) hnum (sq_pos_of_pos hg) hden
  calc
    _ ≤ (2*(max A r⁻¹)^N/(1-r^2)^2)*(P^N*Real.exp (-κ*(N:ℝ)^2))*
        ∏ i, ‖residueFactor (z i)‖ := by
      simp only [signedCanceledDensity,signedGlobalFactor,norm_mul,norm_prod]
      gcongr
    _ = _ := by rw [mul_pow]; ring

end
end IsingBulk.HT.Contour
