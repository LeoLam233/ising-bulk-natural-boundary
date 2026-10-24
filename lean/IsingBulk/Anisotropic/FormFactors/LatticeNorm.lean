import IsingBulk.Anisotropic.FormFactors.ContourNorm

namespace IsingBulk.Anisotropic.FormFactors
noncomputable section
open IsingBulk.First IsingBulk.HT.Contour
open scoped BigOperators

theorem commonDensity_norm_le (N : ℕ) {lam r M A : ℝ} {z : ℂ}
    (_hM : 0 ≤ M)
    (hD : ∀ x y : ℂ, ‖x‖=r → ‖y‖=r → ‖(sliceDispersion lam z x y)⁻¹‖ ≤ M)
    (x y : Fin N → ℂ) (hx : ∀ i, ‖x i‖=r) (hy : ∀ i, ‖y i‖=r)
    (hA : ‖First.pairProduct x‖*‖First.pairProduct y‖ ≤ A) :
    ‖commonDensity lam z x y‖ ≤ A*M^N := by
  have hprod : ‖∏ i,(sliceDispersion lam z (x i) (y i))⁻¹‖ ≤ M^N := by
    rw [norm_prod]
    calc
      _ ≤ ∏ _i : Fin N, M := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        (fun i _ => hD _ _ (hx i) (hy i))
      _ = _ := by simp
  have hA0 : 0 ≤ A := (mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans hA
  unfold commonDensity
  simp only [norm_mul]
  exact mul_le_mul hA hprod (norm_nonneg _) hA0

theorem unscaledLatticeCoefficientAtRadius_norm_le (N : ℕ) {lam r M A : ℝ} {z : ℂ}
    (hr : 0 < r) (hM : 0 ≤ M)
    (hD : ∀ x y : ℂ, ‖x‖=r → ‖y‖=r → ‖(sliceDispersion lam z x y)⁻¹‖ ≤ M)
    (hA : ∀ x y : Fin N → ℂ, (∀ i, ‖x i‖=r) → (∀ i, ‖y i‖=r) →
      ‖First.pairProduct x‖*‖First.pairProduct y‖ ≤ A) (v : ℤ × ℤ) :
    ‖unscaledLatticeCoefficientAtRadius N r lam z v‖ ≤
      (A*M^N/(N.factorial:ℝ))*((r^N)^v.1.natAbs*(r^N)^v.2.natAbs) := by
  have hd (x y : Fin N → ℂ) (hx : ∀ i, ‖x i‖=r) (hy : ∀ i, ‖y i‖=r) :
      ‖onsiteDensity lam z x y*(coordinateProduct x)^v.1.natAbs*(coordinateProduct y)^v.2.natAbs‖ ≤
      (r^N*r^N)⁻¹*(A*M^N)*((r^N)^v.1.natAbs*(r^N)^v.2.natAbs) := by
    have hX : ‖coordinateProduct x‖=r^N := by simp [coordinateProduct,norm_prod,hx]
    have hY : ‖coordinateProduct y‖=r^N := by simp [coordinateProduct,norm_prod,hy]
    have hc := commonDensity_norm_le N hM hD x y hx hy (hA x y hx hy)
    have hh := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ (r^N*r^N)⁻¹)
    have hh' := mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ (r^N)^v.1.natAbs*(r^N)^v.2.natAbs)
    simpa only [onsiteDensity,norm_mul,norm_inv,norm_pow,hX,hY,mul_assoc] using hh'
  have hinner (y : Fin N → ℂ) (hy : ∀ i, ‖y i‖=r) :=
    multiCircleIntegral_norm_le N hr.le _ (fun x hx => hd x y hx hy)
  have hout := multiCircleIntegral_norm_le N hr.le _ (fun y hy => hinner y hy)
  have hh := mul_le_mul_of_nonneg_left hout (by positivity : 0 ≤ (N.factorial:ℝ)⁻¹)
  unfold unscaledLatticeCoefficientAtRadius
  rw [norm_mul,norm_inv,Complex.norm_natCast]
  convert hh using 1
  field_simp

theorem real_geometric_lattice_sum {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    (∑' v : ℤ × ℤ, a^v.1.natAbs*a^v.2.natAbs) = ((1+a)/(1-a))^2 := by
  apply Complex.ofReal_injective
  push_cast
  have hh := physical_geometric_lattice_sum
    (x := (a:ℂ)) (y := (a:ℂ)) (by simpa [Complex.norm_real,abs_of_nonneg ha] using ha1)
    (by simpa [Complex.norm_real,abs_of_nonneg ha] using ha1)
  simpa only [pow_two] using hh

theorem unscaledLatticeCoefficientAtRadius_norm_tsum_le (N : ℕ) (hN : 0 < N)
    {lam r M A : ℝ} {z : ℂ} (hr : 0 < r) (hr1 : r < 1) (hM : 0 ≤ M) (_hA0 : 0 ≤ A)
    (hD : ∀ x y : ℂ, ‖x‖=r → ‖y‖=r → ‖(sliceDispersion lam z x y)⁻¹‖ ≤ M)
    (hA : ∀ x y : Fin N → ℂ, (∀ i, ‖x i‖=r) → (∀ i, ‖y i‖=r) →
      ‖First.pairProduct x‖*‖First.pairProduct y‖ ≤ A) :
    (∑' v : ℤ × ℤ, ‖unscaledLatticeCoefficientAtRadius N r lam z v‖) ≤
      (A*M^N/(N.factorial:ℝ))*((1+r^N)/(1-r^N))^2 := by
  have ha : 0 ≤ r^N := pow_nonneg hr.le N
  have ha1 : r^N < 1 := pow_lt_one₀ hr.le hr1 hN.ne'
  have hs := physical_real_twoSided_geometric_summable ha ha1
  have hprod := hs.mul_of_nonneg hs (fun _ => by positivity) (fun _ => by positivity)
  have hsum := hprod.mul_left (A*M^N/(N.factorial:ℝ))
  have hbound := unscaledLatticeCoefficientAtRadius_norm_le N hr hM hD hA
  calc
    _ ≤ ∑' v : ℤ × ℤ, (A*M^N/(N.factorial:ℝ))*((r^N)^v.1.natAbs*(r^N)^v.2.natAbs) :=
      Summable.tsum_le_tsum hbound
        (hsum.of_nonneg_of_le (fun _ => norm_nonneg _) hbound) hsum
    _ = _ := by rw [tsum_mul_left,real_geometric_lattice_sum ha ha1]
end
end IsingBulk.Anisotropic.FormFactors
