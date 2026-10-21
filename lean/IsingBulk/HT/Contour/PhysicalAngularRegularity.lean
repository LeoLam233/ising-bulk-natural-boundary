import IsingBulk.HT.Contour.PhysicalAngular

/-!
# Real-domain regularity and a uniform physical root-product contraction

The bound is uniform in all angular coordinates, including the dependent
angle. It comes from the actual positive rapidity at angle zero. This is the
geometric domination needed before summing vertical lattice displacements.
-/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First
open scoped BigOperators

theorem physicalGamma_continuous {t : ℝ} (ht : 1 < t) :
    Continuous (physicalGamma t) := by
  apply continuous_iff_continuousAt.mpr
  intro phi
  exact (Real.differentiableAt_arcosh (physical_W_gt_one ht phi)).continuousAt.comp
    (f := fun u : ℝ => t+t⁻¹-Real.cos u) (by fun_prop)

theorem physicalRoot_continuous {t : ℝ} (ht : 1 < t) :
    Continuous (physicalRoot t) :=
  Real.continuous_exp.comp (physicalGamma_continuous ht).neg

theorem physicalZ_continuous (N : ℕ) {t : ℝ} (ht : 1 < t) :
    Continuous (physicalZ (N := N) t) := by
  apply continuous_finsetProd
  intro i _
  exact (physicalRoot_continuous ht).comp (continuous_apply i)

theorem physicalPairProduct_continuous (N : ℕ) {t : ℝ} (ht : 1 < t) :
    Continuous (physicalPairProduct (N := N) t) := by
  have hg (i : Fin N) : Continuous (fun phi : Fin N → ℝ => physicalGamma t (phi i)) :=
    (physicalGamma_continuous ht).comp (continuous_apply i)
  apply continuous_finsetProd
  intro i _
  apply continuous_finsetProd
  intro j _
  apply Continuous.pow
  apply Continuous.div
  · exact Real.continuous_sin.comp (((continuous_apply i).sub (continuous_apply j)).div_const 2)
  · exact Real.continuous_sinh.comp (((hg i).add (hg j)).div_const 2)
  · intro phi
    apply ne_of_gt
    apply Real.sinh_pos_iff.mpr
    linarith [physicalGamma_pos ht (phi i),physicalGamma_pos ht (phi j)]

theorem physicalAngularWeight_continuous (N : ℕ) {t : ℝ} (ht : 1 < t) :
    Continuous (physicalAngularWeight (N := N) t) := by
  apply Continuous.mul _ (physicalPairProduct_continuous N ht)
  apply continuous_finsetProd
  intro i _
  apply Continuous.inv₀
  · exact Real.continuous_sinh.comp
      ((physicalGamma_continuous ht).comp (continuous_apply i))
  · intro phi
    exact (Real.sinh_pos_iff.mpr (physicalGamma_pos ht (phi i))).ne'

/-- The zero-angle rapidity is the smallest physical rapidity. -/
theorem physicalGamma_zero_le {t : ℝ} (ht : 1 < t) (phi : ℝ) :
    physicalGamma t 0 ≤ physicalGamma t phi := by
  unfold physicalGamma
  apply (Real.arcosh_le_arcosh
    (lt_trans zero_lt_one (physical_W_gt_one ht 0))
    (lt_trans zero_lt_one (physical_W_gt_one ht phi))).mpr
  rw [Real.cos_zero]
  linarith [Real.cos_le_one phi]

theorem physicalRoot_le_zero {t : ℝ} (ht : 1 < t) (phi : ℝ) :
    physicalRoot t phi ≤ physicalRoot t 0 :=
  Real.exp_le_exp.mpr (neg_le_neg (physicalGamma_zero_le ht phi))

theorem physicalZ_pos {N : ℕ} {t : ℝ} (ht : 1 < t) (phi : Fin N → ℝ) :
    0 < physicalZ t phi :=
  Finset.prod_pos (fun i _ => (physicalRoot_bounds ht (phi i)).1)

theorem physicalZ_le_zero_pow {N : ℕ} {t : ℝ} (ht : 1 < t) (phi : Fin N → ℝ) :
    physicalZ t phi ≤ (physicalRoot t 0)^N := by
  calc
    physicalZ t phi ≤ ∏ _i : Fin N,physicalRoot t 0 :=
      Finset.prod_le_prod₀
        (fun i _ => (physicalRoot_bounds ht (phi i)).1.le)
        (fun i _ => physicalRoot_le_zero ht (phi i))
    _ = _ := by simp

theorem physicalZ_lt_one {N : ℕ} (hN : 0 < N) {t : ℝ} (ht : 1 < t)
    (phi : Fin N → ℝ) : physicalZ t phi < 1 :=
  (physicalZ_le_zero_pow ht phi).trans_lt
    (pow_lt_one₀ (physicalRoot_bounds ht 0).1.le (physicalRoot_bounds ht 0).2 hN.ne')

theorem physicalDependentAngles_continuous (n : ℕ) :
    Continuous (physicalDependentAngles n) := by
  unfold physicalDependentAngles
  fun_prop

end
end IsingBulk.HT.Contour
