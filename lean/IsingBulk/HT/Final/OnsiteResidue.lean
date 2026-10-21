import IsingBulk.First.ResidueIntegral
import IsingBulk.First.FormFactorNormalization

/-! Actual onsite residue reduction, with the same all-N Cauchy infrastructure
as the established LT contour library. The onsite numerator has no global
product poles. Every apparent x_i=0 pole is canceled before Cauchy is applied. -/
namespace IsingBulk.HT.Final
noncomputable section
open IsingBulk.First Set
open scoped BigOperators

def reducedOnsiteDensity {N : ℕ} (z y : Fin N → ℂ) : ℂ :=
  (coordinateProduct z*coordinateProduct y)⁻¹ *
    pairProduct z * pairProduct y * ∏ i, residueFactor (z i)

def reducedOnsiteFormFactor (N : ℕ) (r : ℝ) (z : ℂ → ℂ) : ℂ :=
  (N.factorial:ℂ)⁻¹ * multiCircleIntegral r N (fun y =>
    reducedOnsiteDensity (fun i => z (y i)) y)

def clearedOnsiteNumerator {N : ℕ} (z y x : Fin N → ℂ) : ℂ :=
  (coordinateProduct y)⁻¹ * pairProduct x * pairProduct y *
    ∏ i, (-2:ℂ)/(x i-(z i)⁻¹)

theorem onsiteDensity_eq_cauchy {N : ℕ} {r : ℝ} {t : ℂ}
    {y z : Fin N → ℂ} (h : ResidueAdmissible r t y z)
    (x : Fin N → ℂ) (hx : ∀ i, x i ≠ 0) :
    onsiteDensity t x y = (∏ i,(x i-z i)⁻¹)*clearedOnsiteNumerator z y x := by
  have hX : coordinateProduct x ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hx i)
  have hp : (∏ i,(dispersion (x i) (y i) t)⁻¹) =
      coordinateProduct x*(∏ i,(x i-z i)⁻¹)*(∏ i,(-2:ℂ)/(x i-(z i)⁻¹)) := by
    simp_rw [dispersion_inv_factorization (hx _) (h.y_ne_zero _)
      (h.root_ne_zero _) (h.root_quadratic _)]
    simp only [Finset.prod_mul_distrib,coordinateProduct]
  have hc : (coordinateProduct x*coordinateProduct y)⁻¹*coordinateProduct x =
      (coordinateProduct y)⁻¹ := by
    rw [mul_inv_rev,mul_assoc,inv_mul_cancel₀ hX,mul_one]
  unfold onsiteDensity commonDensity clearedOnsiteNumerator
  rw [hp]
  calc
    _ = ((coordinateProduct x*coordinateProduct y)⁻¹*coordinateProduct x)*
      pairProduct x*pairProduct y*(∏ i,(x i-z i)⁻¹)*
      (∏ i,(-2:ℂ)/(x i-(z i)⁻¹)) := by ring
    _ = _ := by rw [hc]; ring

theorem clearedOnsiteNumerator_differentiableAt {N : ℕ} {r : ℝ} {t : ℂ}
    {y z : Fin N → ℂ} (h : ResidueAdmissible r t y z)
    (x : Fin N → ℂ) (hx : x ∈ closedPolydisk N r) :
    DifferentiableAt ℂ (clearedOnsiteNumerator z y) x := by
  have hxn : ∀ i, ‖x i‖ < 1 := fun i => (hx i).trans_lt h.radius_lt_one
  have hl : DifferentiableAt ℂ (fun x : Fin N → ℂ =>
      ∏ i,(-2:ℂ)/(x i-(z i)⁻¹)) x := by
    apply finite_product_differentiableAt
    intro i _
    have hi : DifferentiableAt ℂ (fun u : Fin N → ℂ => u i-(z i)⁻¹) x :=
      (differentiableAt_apply i x).sub_const _
    convert! (hi.inv (exterior_root_ne_on_disk h.radius_lt_one
      (hx i) (h.root_inside i) (h.root_ne_zero i))).const_mul (-2:ℂ) using 1
  exact (((pairProduct_differentiableAt x hxn).const_mul
    (coordinateProduct y)⁻¹).mul_const (pairProduct y)).mul hl

theorem clearedOnsiteNumerator_at_roots {N : ℕ} {z y : Fin N → ℂ}
    (hz : ∀ i, z i ≠ 0) :
    clearedOnsiteNumerator z y z = reducedOnsiteDensity z y := by
  have hp : (∏ i,(-2:ℂ)/(z i-(z i)⁻¹)) =
      (coordinateProduct z)⁻¹*∏ i,residueFactor (z i) := by
    simp_rw [residueFactor_cleared (hz _)]
    simp only [Finset.prod_mul_distrib,coordinateProduct,Finset.prod_inv_distrib]
  unfold clearedOnsiteNumerator reducedOnsiteDensity
  rw [hp,mul_inv_rev]
  ring

/-- This is a contour identity for every dimension, before any particle sum. -/
theorem onsite_residue_inner_integral {N : ℕ} {r : ℝ} {t : ℂ}
    {y z : Fin N → ℂ} (h : ResidueAdmissible r t y z) :
    multiCircleIntegral r N (fun x => onsiteDensity t x y) =
      reducedOnsiteDensity z y := by
  calc
    _ = multiCircleIntegral r N (fun x =>
        (∏ i,(x i-z i)⁻¹)*clearedOnsiteNumerator z y x) := by
      apply multiCircleIntegral_congr h.radius_pos.le N
      intro x hx
      apply onsiteDensity_eq_cauchy h x
      intro i hi
      have hh := hx i
      simp [hi] at hh
      linarith [h.radius_pos]
    _ = clearedOnsiteNumerator z y z := multiCircleIntegral_cauchy h.radius_pos N _ z
      h.root_inside (clearedOnsiteNumerator_differentiableAt h)
    _ = _ := clearedOnsiteNumerator_at_roots h.root_ne_zero

theorem onsite_residue_reduction (N : ℕ) (r : ℝ) (hr : 0 < r)
    (t : ℂ) (z : ℂ → ℂ)
    (h : ∀ y ∈ productCircle N r, ResidueAdmissible r t y (fun i => z (y i))) :
    onsiteFormFactor N r t = reducedOnsiteFormFactor N r z := by
  unfold onsiteFormFactor reducedOnsiteFormFactor
  congr 1
  apply multiCircleIntegral_congr hr.le N
  intro y hy
  exact onsite_residue_inner_integral (h y hy)

end
end IsingBulk.HT.Final
