import IsingBulk.HT.Contour.PhysicalOnsiteAttachment

/-!
# Double-contour lift of every physical nonnegative lattice displacement

The residue numerator is multiplied by the actual polynomial X^m before
Cauchy reduction. Thus the source's lattice symmetry can subsequently be
proved by exchanging the genuine x and y contour families, not postulated
from an unrelated angular integral.
-/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Final Set
open scoped BigOperators

theorem physical_displaced_onsite_analyticAt {N : ℕ} {s : ℂ} (hs : s ≠ 0)
    {y : Fin N → ℂ} (hy : ∀ i,y i ≠ 0)
    (hW : ∀ i,1 < (sourceW s (y i)).re) (m n : ℕ) :
    AnalyticAt ℂ (fun v : Fin N → ℂ =>
      onsiteCanceledDensity (fun i => rightRoot s (v i)) v *
        (coordinateProduct (fun i => rightRoot s (v i)))^m *
        (coordinateProduct v)^n) y := by
  have dy (i : Fin N) : AnalyticAt ℂ (fun v : Fin N → ℂ => v i) y :=
    (ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ).analyticAt y
  have dW (i : Fin N) : AnalyticAt ℂ (fun v : Fin N → ℂ => sourceW s (v i)) y :=
    analyticAt_const.sub (((dy i).add ((dy i).inv (hy i))).div analyticAt_const (by norm_num))
  have dz (i : Fin N) : AnalyticAt ℂ (fun v : Fin N → ℂ => rightRoot s (v i)) y :=
    (compactLeftRoot_analyticAt (hW i)).comp
      (f := fun v : Fin N → ℂ => sourceW s (v i)) (dW i)
  have dY : AnalyticAt ℂ (fun v : Fin N → ℂ => coordinateProduct v) y :=
    Finset.analyticAt_fun_prod _ (fun i _ => dy i)
  have dZ : AnalyticAt ℂ
      (fun v : Fin N → ℂ => coordinateProduct (fun i => rightRoot s (v i))) y :=
    Finset.analyticAt_fun_prod _ (fun i _ => dz i)
  exact ((physical_onsiteCanceledDensity_analyticAt hs hy hW).mul (dZ.pow m)).mul (dY.pow n)

theorem physicalLatticeCoefficient_eq_interior_contour (N m n : ℕ) {t r : ℝ}
    (ht : 1 < t) (hr : 0 < r) (hr1 : r < 1)
    (hm : 1+r⁻¹ < (sourceS (t:ℂ)).re) :
    physicalLatticeCoefficient N t m (n:ℤ) =
      (N.factorial:ℂ)⁻¹ * multiCircleIntegral r N (fun y =>
        onsiteCanceledDensity (fun i => rightRoot (t:ℂ) (y i)) y *
          (coordinateProduct (fun i => rightRoot (t:ℂ) (y i)))^m *
          (coordinateProduct y)^n) := by
  have ht0 : (t:ℂ) ≠ 0 := by exact_mod_cast (lt_trans zero_lt_one ht).ne'
  rw [physicalLatticeCoefficient_eq_unit_contour N ht m (n:ℤ)]
  simp only [zpow_natCast]
  congr 1
  apply multiCircleIntegral_radius_eq N hr hr1.le
  intro y hy
  exact (physical_displaced_onsite_analyticAt ht0
    (fun i => norm_pos_iff.mp (hr.trans_le (hy i).1))
    (fun i => physical_sourceW_right_on_annulus hr hr1 hm (hy i).1 (hy i).2)
    m n).differentiableAt

/-- Polynomial displacement is carried through the actual multivariate
Cauchy reduction; it is not an assumed physical residue rule. -/
theorem physical_displaced_onsite_residue_inner {N : ℕ} {r : ℝ} {s : ℂ}
    {y z : Fin N → ℂ} (h : ResidueAdmissible r s y z) (m : ℕ) :
    multiCircleIntegral r N (fun x => (coordinateProduct x)^m*onsiteDensity s x y) =
      (coordinateProduct z)^m*reducedOnsiteDensity z y := by
  calc
    _ = multiCircleIntegral r N (fun x =>
        (∏ i,(x i-z i)⁻¹) *
          ((coordinateProduct x)^m*clearedOnsiteNumerator z y x)) := by
      apply multiCircleIntegral_congr h.radius_pos.le N
      intro x hx
      have hx0 (i : Fin N) : x i ≠ 0 :=
        norm_ne_zero_iff.mp ((hx i).trans_ne h.radius_pos.ne')
      rw [onsiteDensity_eq_cauchy h x hx0]
      ring
    _ = (coordinateProduct z)^m*clearedOnsiteNumerator z y z := by
      apply multiCircleIntegral_cauchy h.radius_pos N _ z h.root_inside
      intro x hx
      exact ((coordinateProduct_differentiableAt x).pow m).mul
        (clearedOnsiteNumerator_differentiableAt h x hx)
    _ = _ := by rw [clearedOnsiteNumerator_at_roots h.root_ne_zero]

/-- The genuine double-contour lift of q_N(m,n) in the nonnegative quadrant,
including the origin and both axes. The same onsite density is reused. -/
theorem physicalLatticeCoefficient_eq_double_contour (N m n : ℕ) {t r : ℝ}
    (ht : 1 < t) (hr : 0 < r) (hr1 : r < 1)
    (hm : 1+r⁻¹ < (sourceS (t:ℂ)).re) :
    physicalLatticeCoefficient N t m (n:ℤ) =
      (N.factorial:ℂ)⁻¹ * multiCircleIntegral r N (fun y =>
        (coordinateProduct y)^n * multiCircleIntegral r N
          (fun x => (coordinateProduct x)^m*onsiteDensity (t:ℂ) x y)) := by
  rw [physicalLatticeCoefficient_eq_interior_contour N m n ht hr hr1 hm]
  congr 1
  apply multiCircleIntegral_congr hr.le N
  intro y hy
  have h := (rightRoot_admissible hr hr1 hm).toTuple N y hy
  rw [physical_displaced_onsite_residue_inner h m]
  have hW (i : Fin N) : 1 < (sourceW (t:ℂ) (y i)).re :=
    sourceW_right_of_margin hr hr1 hm (hy i)
  have he : (fun i => selectedContinuedRoot (t:ℂ) (y i)) =
      (fun i => rightRoot (t:ℂ) (y i)) := by
    funext i
    simp only [selectedContinuedRoot,continuedRoot,ite_eq_left (hW i),rightRoot]
  have hd := onsite_canceledReducedDensity_continued_eq (t:ℂ) y
    (fun i => norm_ne_zero_iff.mp ((hy i).trans_ne hr.ne'))
    (fun i => Or.inl (Or.inr (hW i)))
    (fun i j => one_sub_mul_ne_zero_of_norm_lt_one
      ((hy i).trans_lt hr1) ((hy j).trans_lt hr1))
  rw [he] at hd
  rw [hd]
  ring

end
end IsingBulk.HT.Contour
