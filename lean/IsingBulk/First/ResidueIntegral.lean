import IsingBulk.First.NormalizedContour
import IsingBulk.First.ResidueCancellation

/-! Residue reduction of the complete normalized source double integral. -/
namespace IsingBulk.First
noncomputable section
open scoped BigOperators
open Set

theorem finite_product_differentiableAt {N : ℕ} {ι : Type*} [DecidableEq ι]
    (t : Finset ι) (f : ι → (Fin N → ℂ) → ℂ) (x : Fin N → ℂ)
    (hf : ∀ i ∈ t, DifferentiableAt ℂ (f i) x) :
    DifferentiableAt ℂ (fun y => ∏ i ∈ t, f i y) x :=
  (HasFDerivAt.finsetProd (fun i hi => (hf i hi).hasFDerivAt)).differentiableAt

theorem coordinateProduct_differentiableAt {N : ℕ} (x : Fin N → ℂ) :
    DifferentiableAt ℂ coordinateProduct x := by
  exact finite_product_differentiableAt Finset.univ (fun i y => y i) x
    (fun i _ => differentiableAt_apply i x)

theorem pairProduct_differentiableAt {N : ℕ} (x : Fin N → ℂ)
    (hx : ∀ i, ‖x i‖ < 1) : DifferentiableAt ℂ pairProduct x := by
  unfold pairProduct
  apply finite_product_differentiableAt
  intro i _
  apply finite_product_differentiableAt
  intro j _
  change DifferentiableAt ℂ (fun y : Fin N → ℂ => (y i-y j)/(1-y i*y j)) x
  have hi : DifferentiableAt ℂ (fun u : Fin N → ℂ => u i) x := differentiableAt_apply i x
  have hj : DifferentiableAt ℂ (fun u : Fin N → ℂ => u j) x := differentiableAt_apply j x
  have hnum : DifferentiableAt ℂ (fun u : Fin N → ℂ => u i-u j) x := hi.sub hj
  have hden : DifferentiableAt ℂ (fun u : Fin N → ℂ => 1-u i*u j) x := (hi.mul hj).const_sub 1
  convert! hnum.mul (hden.inv (one_sub_mul_ne_zero_of_norm_lt_one (hx i) (hx j))) using 1

theorem clearedNumerator_differentiableAt {N : ℕ} (hN : 0 < N) {r : ℝ} {s : ℂ}
    {y z : Fin N → ℂ} (h : ResidueAdmissible r s y z)
    (x : Fin N → ℂ) (hx : x ∈ closedPolydisk N r) :
    DifferentiableAt ℂ (clearedNumerator z y) x := by
  have hxn : ∀ i, ‖x i‖ < 1 := fun i => (hx i).trans_lt h.radius_lt_one
  have hyn : ∀ i, ‖y i‖ < 1 := fun i => by rw [h.y_on_circle i]; exact h.radius_lt_one
  have hX := one_sub_coordinateProduct_ne_zero hN hxn
  have hY := one_sub_coordinateProduct_ne_zero hN hyn
  have hp := coordinateProduct_differentiableAt x
  have hlocal : DifferentiableAt ℂ (fun x : Fin N → ℂ => ∏ i, (-2:ℂ)/(x i-(z i)⁻¹)) x := by
    apply finite_product_differentiableAt
    intro i _
    have hi : DifferentiableAt ℂ (fun u : Fin N → ℂ => u i-(z i)⁻¹) x :=
      (differentiableAt_apply i x).sub_const _
    convert! (hi.inv
      (exterior_root_ne_on_disk h.radius_lt_one (hx i) (h.root_inside i) (h.root_ne_zero i))).const_mul (-2:ℂ) using 1
  have hnum : DifferentiableAt ℂ (fun u : Fin N → ℂ => 1+coordinateProduct u/coordinateProduct y) x :=
    by simpa only [div_eq_mul_inv] using (hp.mul_const (coordinateProduct y)⁻¹).const_add 1
  have hden : DifferentiableAt ℂ
      (fun u : Fin N → ℂ => (1-coordinateProduct u)*(1-coordinateProduct y)) x :=
    (hp.const_sub 1).mul_const _
  have hquot : DifferentiableAt ℂ (fun u : Fin N → ℂ =>
      (1+coordinateProduct u/coordinateProduct y)/((1-coordinateProduct u)*(1-coordinateProduct y))) x := by
    convert! hnum.mul (hden.inv (mul_ne_zero hX hY)) using 1
  exact ((hquot.mul (pairProduct_differentiableAt x hxn)).mul_const (pairProduct y)).mul hlocal

/-- Actual successive normalized x residues; all apparent zero poles were
removed in the complete numerator before applying Cauchy's theorem. -/
theorem residue_inner_integral {N : ℕ} (hN : 0 < N) {r : ℝ} {s : ℂ}
    {y z : Fin N → ℂ} (h : ResidueAdmissible r s y z) :
    multiCircleIntegral r N (fun x => doubleDensity s x y) = reducedDensity z y := by
  calc
    _ = multiCircleIntegral r N (fun x => (∏ i, (x i-z i)⁻¹)*clearedNumerator z y x) := by
      apply multiCircleIntegral_congr h.radius_pos.le N
      intro x hx
      apply doubleDensity_eq_cauchy h x
      intro i hi
      have hh := hx i
      simp [hi] at hh
      linarith [h.radius_pos]
    _ = clearedNumerator z y z := multiCircleIntegral_cauchy h.radius_pos N _ z h.root_inside
      (clearedNumerator_differentiableAt hN h)
    _ = _ := clearedNumerator_at_roots h.root_ne_zero

/-- Source-facing normalized double-to-reduced integral equality. No residue,
integral, or holomorphy conclusion is a hypothesis. -/
theorem residue_reduction (N : ℕ) (hN : 0 < N) (r : ℝ) (hr : 0 < r)
    (s : ℂ) (z : ℂ → ℂ)
    (h : ∀ y ∈ productCircle N r, ResidueAdmissible r s y (fun i => z (y i))) :
    doubleFormFactor N r s = reducedFormFactor N r z := by
  unfold doubleFormFactor reducedFormFactor
  congr 1
  apply multiCircleIntegral_congr hr.le N
  intro y hy
  exact residue_inner_integral hN (h y hy)

end
end IsingBulk.First
