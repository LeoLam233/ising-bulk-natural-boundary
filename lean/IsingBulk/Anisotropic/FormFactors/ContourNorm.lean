import IsingBulk.Anisotropic.FormFactors.FullLatticeContour
import IsingBulk.First.ContourNormBounds

namespace IsingBulk.Anisotropic.FormFactors
noncomputable section
open IsingBulk.First IsingBulk.HT.Contour
open scoped BigOperators

theorem ratio_norm_le {r : ℝ} (hr : r < 1) {X : ℂ} (hX : ‖X‖ ≤ r) :
    ‖(1+X)/(1-X)‖ ≤ 2/(1-r) := by
  have hden : 1-r ≤ ‖1-X‖ := by
    have hh := norm_sub_norm_le (1:ℂ) X
    norm_num at hh
    linarith
  have hnum : ‖1+X‖ ≤ 2 := by
    have hh := norm_add_le (1:ℂ) X
    norm_num at hh
    linarith
  rw [norm_div]
  exact div_le_div₀ (by norm_num) hnum (by linarith) hden

theorem fullDensity_norm_le (N : ℕ) (hN : 0 < N) {lam r M A : ℝ} {z : ℂ}
    (hr : 0 < r) (hr1 : r < 1) (_hM : 0 ≤ M)
    (hD : ∀ x y : ℂ, ‖x‖=r → ‖y‖=r → ‖(sliceDispersion lam z x y)⁻¹‖ ≤ M)
    (x y : Fin N → ℂ) (hx : ∀ i, ‖x i‖=r) (hy : ∀ i, ‖y i‖=r)
    (hA : ‖First.pairProduct x‖*‖First.pairProduct y‖ ≤ A) :
    ‖fullDensity lam z x y‖ ≤ (r^N)⁻¹*(r^N)⁻¹*(2/(1-r))^2*A*M^N := by
  have hX : ‖coordinateProduct x‖=r^N := by simp [coordinateProduct,norm_prod,hx]
  have hY : ‖coordinateProduct y‖=r^N := by simp [coordinateProduct,norm_prod,hy]
  have hp : r^N ≤ r := by
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
    rw [pow_succ]
    exact mul_le_of_le_one_left hr.le (pow_le_one₀ hr.le hr1.le)
  have hxrat := ratio_norm_le hr1 (hX.le.trans hp)
  have hyrat := ratio_norm_le hr1 (hY.le.trans hp)
  have hMprod : ‖∏ i,(sliceDispersion lam z (x i) (y i))⁻¹‖ ≤ M^N := by
    rw [norm_prod]
    calc
      _ ≤ ∏ _i : Fin N, M := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hD _ _ (hx i) (hy i))
      _ = _ := by simp
  have he : fullDensity lam z x y =
      (coordinateProduct x)⁻¹*(coordinateProduct y)⁻¹ *
        ((1+coordinateProduct x)/(1-coordinateProduct x))*
        ((1+coordinateProduct y)/(1-coordinateProduct y))*
        (First.pairProduct x*First.pairProduct y)*
        (∏ i,(sliceDispersion lam z (x i) (y i))⁻¹) := by
    unfold fullDensity commonDensity
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [he]
  simp only [norm_mul,norm_inv,hX,hY]
  have hrat := mul_le_mul hxrat hyrat (norm_nonneg _) (by positivity : (0:ℝ) ≤ 2/(1-r))
  have hpairs := mul_le_mul hrat hA (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
  have hall := mul_le_mul hpairs hMprod (norm_nonneg _) (by
    have : 0 ≤ A := (mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans hA
    positivity)
  have hh := mul_le_mul_of_nonneg_left hall (by positivity : 0 ≤ (r^N)⁻¹*(r^N)⁻¹)
  nlinarith only [hh]

/-- The normalized double circles cancel every radial Jacobian loss.
This is a finite integral inequality, not a normal-convergence assumption. -/
theorem unscaledFullCoefficientAtRadius_norm_le (N : ℕ) (hN : 0 < N)
    {lam r M A : ℝ} {z : ℂ} (hr : 0 < r) (hr1 : r < 1) (hM : 0 ≤ M)
    (hD : ∀ x y : ℂ, ‖x‖=r → ‖y‖=r → ‖(sliceDispersion lam z x y)⁻¹‖ ≤ M)
    (hA : ∀ x y : Fin N → ℂ, (∀ i, ‖x i‖=r) → (∀ i, ‖y i‖=r) →
      ‖First.pairProduct x‖*‖First.pairProduct y‖ ≤ A) :
    ‖unscaledFullCoefficientAtRadius N r lam z‖ ≤
      (2/(1-r))^2*A*M^N/(N.factorial:ℝ) := by
  have hinner (y : Fin N → ℂ) (hy : ∀ i, ‖y i‖=r) :=
    multiCircleIntegral_norm_le N hr.le (fun x => fullDensity lam z x y)
      (fun x hx => fullDensity_norm_le N hN hr hr1 hM hD x y hx hy (hA x y hx hy))
  have hout := multiCircleIntegral_norm_le N hr.le
    (fun y => multiCircleIntegral r N (fun x => fullDensity lam z x y))
    (fun y hy => hinner y hy)
  have hh := mul_le_mul_of_nonneg_left hout (by positivity : 0 ≤ (N.factorial:ℝ)⁻¹)
  unfold unscaledFullCoefficientAtRadius
  rw [norm_mul,norm_inv,Complex.norm_natCast]
  convert hh using 1
  field_simp
end
end IsingBulk.Anisotropic.FormFactors
