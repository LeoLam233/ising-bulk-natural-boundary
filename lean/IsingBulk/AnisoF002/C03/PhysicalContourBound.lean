import IsingBulk.AnisoF002.C03.PhysicalContourSchur

/-!
# Exact full-contour coefficient bounds

Every inverse dispersion, every Schur pair, and the full two-variable site
multiplier is retained.  The normalized contour norms supply exactly the
radial powers which cancel the multiplier's coordinate-product inverses.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set Metric IsingBulk.First IsingBulk.Anisotropic
  IsingBulk.Anisotropic.FormFactors
open scoped BigOperators

theorem literal_normalizedCircleIntegral_norm_le {r M : ℝ} (hr : 0 ≤ r)
    (f : ℂ → ℂ) (hf : ∀ z, ‖z‖ = r → ‖f z‖ ≤ M) :
    ‖normalizedCircleIntegral r f‖ ≤ r * M := by
  apply circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hr
  intro z hz
  exact hf z (by simpa only [mem_sphere_iff_norm, sub_zero] using hz)

theorem literal_multiCircleIntegral_norm_le (N : ℕ) {r M : ℝ} (hr : 0 ≤ r)
    (f : (Fin N → ℂ) → ℂ) (hf : ∀ x ∈ productCircle N r, ‖f x‖ ≤ M) :
    ‖multiCircleIntegral r N f‖ ≤ r ^ N * M := by
  induction N generalizing M with
  | zero => simpa only [multiCircleIntegral, pow_zero, one_mul] using hf Fin.elim0 (fun i => Fin.elim0 i)
  | succ n ih =>
    have hh := ih (M := r * M) (fun x => normalizedCircleIntegral r (fun z => f (Fin.cons z x))) (by
      intro x hx
      apply literal_normalizedCircleIntegral_norm_le hr
      intro z hz
      apply hf
      intro i
      exact Fin.cases hz (fun j => hx j) i)
    simpa only [multiCircleIntegral, pow_succ, mul_assoc] using hh

theorem literal_siteRatio_bound {r : ℝ} (hr : r < 1) {X : ℂ} (hX : ‖X‖ ≤ r) :
    ‖(1 + X) / (1 - X)‖ ≤ 2 / (1 - r) := by
  have hden : 1 - r ≤ ‖1 - X‖ := by
    have hh := norm_sub_norm_le (1 : ℂ) X
    rw [norm_one] at hh
    linarith
  have hnum : ‖1 + X‖ ≤ 2 := by
    have hh := norm_add_le (1 : ℂ) X
    rw [norm_one] at hh
    linarith
  rw [norm_div]
  exact div_le_div₀ (by norm_num) hnum (by linarith) hden

theorem literal_fullDensity_bound {N : ℕ} (hN : 0 < N) {lam r M A : ℝ} {z : ℂ}
    (hr : 0 < r) (hr1 : r < 1)
    (hD : ∀ x y : ℂ, ‖x‖ = r → ‖y‖ = r → ‖(sliceDispersion lam z x y)⁻¹‖ ≤ M)
    (x y : Fin N → ℂ) (hx : ∀ i, ‖x i‖ = r) (hy : ∀ i, ‖y i‖ = r)
    (hA : ‖First.pairProduct x‖ * ‖First.pairProduct y‖ ≤ A) :
    ‖fullDensity lam z x y‖ ≤ (r ^ N)⁻¹ * (r ^ N)⁻¹ * (2 / (1 - r)) ^ 2 * A * M ^ N := by
  have hX : ‖coordinateProduct x‖ = r ^ N := by simp only [coordinateProduct, norm_prod, hx,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hY : ‖coordinateProduct y‖ = r ^ N := by simp only [coordinateProduct, norm_prod, hy,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hp : r ^ N ≤ r := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
    rw [pow_succ]
    exact mul_le_of_le_one_left hr.le (pow_le_one₀ hr.le hr1.le)
  have hxrat := literal_siteRatio_bound hr1 (hX.le.trans hp)
  have hyrat := literal_siteRatio_bound hr1 (hY.le.trans hp)
  have hMprod : ‖∏ i, (sliceDispersion lam z (x i) (y i))⁻¹‖ ≤ M ^ N := by
    rw [norm_prod]
    calc
      _ ≤ ∏ _i : Fin N, M := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        (fun i _ => hD _ _ (hx i) (hy i))
      _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have he : fullDensity lam z x y =
      (coordinateProduct x)⁻¹ * (coordinateProduct y)⁻¹ *
        ((1 + coordinateProduct x) / (1 - coordinateProduct x)) *
        ((1 + coordinateProduct y) / (1 - coordinateProduct y)) *
        (First.pairProduct x * First.pairProduct y) *
        (∏ i, (sliceDispersion lam z (x i) (y i))⁻¹) := by
    unfold fullDensity FormFactors.commonDensity
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he]
  simp only [norm_mul, norm_inv, hX, hY]
  have hrat := mul_le_mul hxrat hyrat (norm_nonneg _) (by positivity : (0 : ℝ) ≤ 2 / (1 - r))
  have hpairs := mul_le_mul hrat hA (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
  have hall := mul_le_mul hpairs hMprod (norm_nonneg _) (by
    have : 0 ≤ A := (mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans hA
    positivity)
  have hh := mul_le_mul_of_nonneg_left hall (by positivity : 0 ≤ (r ^ N)⁻¹ * (r ^ N)⁻¹)
  nlinarith only [hh]

theorem literal_fixedCoefficient_bound {N : ℕ} (hN : 0 < N)
    {lam r M A : ℝ} {z : ℂ} (hr : 0 < r) (hr1 : r < 1)
    (hD : ∀ x y : ℂ, ‖x‖ = r → ‖y‖ = r → ‖(sliceDispersion lam z x y)⁻¹‖ ≤ M)
    (hA : ∀ x y : Fin N → ℂ, (∀ i, ‖x i‖ = r) → (∀ i, ‖y i‖ = r) →
      ‖First.pairProduct x‖ * ‖First.pairProduct y‖ ≤ A) :
    ‖unscaledFullCoefficientAtRadius N r lam z‖ ≤
      (2 / (1 - r)) ^ 2 * A * M ^ N / (N.factorial : ℝ) := by
  have hinner (y : Fin N → ℂ) (hy : ∀ i, ‖y i‖ = r) :=
    literal_multiCircleIntegral_norm_le N hr.le (fun x => fullDensity lam z x y)
      (fun x hx => literal_fullDensity_bound hN hr hr1 hD x y hx hy (hA x y hx hy))
  have hout := literal_multiCircleIntegral_norm_le N hr.le
    (fun y => multiCircleIntegral r N (fun x => fullDensity lam z x y))
    (fun y hy => hinner y hy)
  have hh := mul_le_mul_of_nonneg_left hout (by positivity : 0 ≤ (N.factorial : ℝ)⁻¹)
  unfold unscaledFullCoefficientAtRadius
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  convert hh using 1
  field_simp

end
end IsingBulk.AnisoF002.RegularTail.C03
