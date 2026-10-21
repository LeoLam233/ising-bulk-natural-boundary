import IsingBulk.HT.Contour.PhysicalAngular
import IsingBulk.Tail.SelectorDefinitions

/-! Exact conversion of every complete canceled pair on the physical unit
circle.  These are source equalities, including reciprocal angular pairs;
there is no division by the removable `1-y_i*y_j` factor. -/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Tail
open scoped BigOperators

theorem limitingAngle_div (a b : ℝ) :
    limitingAngle a/limitingAngle b = limitingAngle (a-b) := by
  unfold limitingAngle
  rw [← Complex.exp_sub]
  congr 1
  push_cast
  ring

theorem limitingAngle_neg (a : ℝ) : limitingAngle (-a)=(limitingAngle a)⁻¹ := by
  unfold limitingAngle
  rw [← Complex.exp_neg]
  congr 1
  push_cast
  ring

theorem physical_unit_pair_numerator (a b : ℝ) :
    -(limitingAngle a-limitingAngle b)^2/(limitingAngle a*limitingAngle b) =
      (4*Real.sin ((a-b)/2)^2:ℝ) := by
  have ha : limitingAngle a ≠ 0 := Complex.exp_ne_zero _
  have hb : limitingAngle b ≠ 0 := Complex.exp_ne_zero _
  have hcos := Real.cos_two_mul_eq_one_sub ((a-b)/2)
  rw [show 2*((a-b)/2)=a-b by ring] at hcos
  calc
    _ = 2-(limitingAngle a/limitingAngle b+limitingAngle b/limitingAngle a) := by
      field_simp
      ring
    _ = 2-(limitingAngle (a-b)+(limitingAngle (a-b))⁻¹) := by
      rw [limitingAngle_div,limitingAngle_div,
        show b-a=-(a-b) by ring,limitingAngle_neg]
    _ = 2-2*(Real.cos (a-b):ℂ) := by rw [limitingAngle_trace]
    _ = _ := by exact_mod_cast (show (2:ℝ)-2*Real.cos (a-b)=4*Real.sin ((a-b)/2)^2 by linarith)

theorem physical_exp_pair_denominator (a b : ℝ) :
    (1-Real.exp (-a)*Real.exp (-b))^2 =
      4*(Real.exp (-a)*Real.exp (-b))*Real.sinh ((a+b)/2)^2 := by
  let h : ℝ := (a+b)/2
  have he : Real.exp (-a)*Real.exp (-b)=(Real.exp (-h))^2 := by
    rw [← Real.exp_add, pow_two, ← Real.exp_add]
    congr 1
    dsimp [h]
    ring
  have he0 : Real.exp h ≠ 0 := (Real.exp_pos h).ne'
  have hid : 1-(Real.exp (-h))^2=2*Real.exp (-h)*Real.sinh h := by
    rw [Real.sinh_eq,Real.exp_neg]
    field_simp
  rw [he]
  change (1-Real.exp (-h)^2)^2=4*Real.exp (-h)^2*Real.sinh h^2
  rw [hid]
  ring

theorem physical_pair_root_ratio {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (Real.exp (-a)*Real.exp (-b))/(1-Real.exp (-a)*Real.exp (-b))^2 =
      (4*Real.sinh ((a+b)/2)^2)⁻¹ := by
  have hs : 0 < Real.sinh ((a+b)/2) := Real.sinh_pos_iff.mpr (by linarith)
  have he : 0 < Real.exp (-a)*Real.exp (-b) := mul_pos (Real.exp_pos _) (Real.exp_pos _)
  rw [physical_exp_pair_denominator]
  field_simp

/-- One actual complete pair, including coincident and reciprocal y values. -/
theorem physical_canceledPair {t : ℝ} (ht : 1 < t) (a b : ℝ) :
    canceledPair (limitingAngle a) (limitingAngle b)
      (rightRoot (t:ℂ) (limitingAngle a)) (rightRoot (t:ℂ) (limitingAngle b)) =
    ((Real.sin ((a-b)/2) /
      Real.sinh ((physicalGamma t a+physicalGamma t b)/2))^2:ℝ) := by
  rw [rightRoot_real_unit_angle ht,rightRoot_real_unit_angle ht]
  have hratio := physical_pair_root_ratio (physicalGamma_pos ht a) (physicalGamma_pos ht b)
  have hratioC : ((physicalRoot t a:ℂ)*(physicalRoot t b:ℂ))/
      (1-(physicalRoot t a:ℂ)*(physicalRoot t b:ℂ))^2 =
      ((4*Real.sinh ((physicalGamma t a+physicalGamma t b)/2)^2)⁻¹:ℝ) := by
    exact_mod_cast hratio
  calc
    _ = (-(limitingAngle a-limitingAngle b)^2/(limitingAngle a*limitingAngle b))*
        (((physicalRoot t a:ℂ)*(physicalRoot t b:ℂ))/
          (1-(physicalRoot t a:ℂ)*(physicalRoot t b:ℂ))^2) := by
      unfold canceledPair
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    _ = _ := by
      rw [physical_unit_pair_numerator,hratioC]
      push_cast
      simp only [div_eq_mul_inv,mul_inv_rev]
      norm_num
      ring

theorem physical_canceledPairProduct {N : ℕ} {t : ℝ} (ht : 1 < t) (phi : Fin N → ℝ) :
    canceledPairProduct (fun i => rightRoot (t:ℂ) (limitingAngle (phi i)))
      (fun i => limitingAngle (phi i)) = (physicalPairProduct t phi:ℂ) := by
  simp only [canceledPairProduct,physicalPairProduct,Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j _
  exact physical_canceledPair ht (phi i) (phi j)

/-- Onsite residue after multiplying by the angular Jacobian, with its full
one-body and complete-pair product; no parity assumption is used. -/
theorem physical_onsite_unit_density {N : ℕ} {t : ℝ} (ht : 1 < t) (phi : Fin N → ℝ) :
    let y := fun i => limitingAngle (phi i)
    let z := fun i => rightRoot (t:ℂ) (y i)
    coordinateProduct y * (coordinateProduct z*coordinateProduct y)⁻¹ *
      canceledPairProduct z y * (∏ i,residueFactor (z i)) =
        (physicalAngularWeight t phi:ℂ) := by
  dsimp only
  rw [physical_canceledPairProduct ht]
  simp_rw [rightRoot_real_unit_angle ht,physical_residueFactor ht]
  have hy : coordinateProduct (fun i => limitingAngle (phi i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => Complex.exp_ne_zero _)
  have hz : coordinateProduct (fun i => (physicalRoot t (phi i):ℂ)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact_mod_cast (physicalRoot_bounds ht (phi i)).1.ne'
  have hprod : (∏ i,((physicalRoot t (phi i)/Real.sinh (physicalGamma t (phi i)):ℝ):ℂ)) =
      coordinateProduct (fun i => (physicalRoot t (phi i):ℂ)) *
        ∏ i,((Real.sinh (physicalGamma t (phi i)))⁻¹:ℝ) := by
    simp only [div_eq_mul_inv,Complex.ofReal_mul,Complex.ofReal_prod,
      Finset.prod_mul_distrib,coordinateProduct]
  rw [hprod]
  unfold physicalAngularWeight
  push_cast
  field_simp

end
end IsingBulk.HT.Contour
