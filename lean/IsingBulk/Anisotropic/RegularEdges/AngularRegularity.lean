import IsingBulk.Anisotropic.FormFactors.LatticeReflection
import IsingBulk.HT.Contour.PhysicalAngularRegularity

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open FormFactors IsingBulk.HT.Contour
open scoped BigOperators

theorem gamma_continuous {B C : ℝ} (hB : 0≤B) (hgap : 1<C-B) : Continuous (gamma B C) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  exact (Real.differentiableAt_arcosh (dispersion_gt_one hB hgap q)).continuousAt.comp
    (f := fun u : ℝ => C-B*Real.cos u) (by fun_prop)

theorem root_continuous {B C : ℝ} (hB : 0≤B) (hgap : 1<C-B) : Continuous (root B C) :=
  Real.continuous_exp.comp (gamma_continuous hB hgap).neg

theorem angularWeight_continuous (N : ℕ) {B C : ℝ} (hB : 0≤B) (hgap : 1<C-B) :
    Continuous (angularWeight (N := N) B C) := by
  have hg (i : Fin N) : Continuous (fun q : Fin N → ℝ => gamma B C (q i)) :=
    (gamma_continuous hB hgap).comp (continuous_apply i)
  unfold angularWeight FormFactors.pairProduct
  refine (continuous_const.mul ?_).mul ?_
  · apply continuous_finsetProd
    intro i _
    exact (Real.continuous_sinh.comp (hg i)).inv₀
      (fun q => (Real.sinh_pos_iff.mpr (gamma_pos hB hgap (q i))).ne')
  · apply continuous_finsetProd
    intro i _
    apply continuous_finsetProd
    intro j _
    apply Continuous.pow
    apply Continuous.div
    · exact Real.continuous_sin.comp (((continuous_apply i).sub (continuous_apply j)).div_const 2)
    · exact Real.continuous_sinh.comp (((hg i).add (hg j)).div_const 2)
    · intro q
      apply (Real.sinh_pos_iff.mpr _).ne'
      linarith [gamma_pos hB hgap (q i),gamma_pos hB hgap (q j)]

theorem rootProduct_continuous (N : ℕ) {B C : ℝ} (hB : 0≤B) (hgap : 1<C-B) : Continuous (rootProduct (N := N) B C) := by
  unfold rootProduct
  exact continuous_finsetProd _ (fun i _ => (root_continuous hB hgap).comp (continuous_apply i))

theorem root_le_zero {B C : ℝ} (hB : 0≤B) (hgap : 1<C-B) (q : ℝ) :
    root B C q≤root B C 0 := by
  unfold root gamma
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  apply (Real.arcosh_le_arcosh (lt_trans zero_lt_one (dispersion_gt_one hB hgap 0))
    (lt_trans zero_lt_one (dispersion_gt_one hB hgap q))).mpr
  simp only [Real.cos_zero,mul_one]
  nlinarith [Real.cos_le_one q]

theorem rootProduct_pos {N : ℕ} {B C : ℝ} (hB : 0≤B) (hgap : 1<C-B) (q : Fin N → ℝ) :
    0<rootProduct B C q := Finset.prod_pos (fun i _ => (root_bounds hB hgap (q i)).1)

theorem rootProduct_le_zero_pow {N : ℕ} {B C : ℝ} (hB : 0≤B) (hgap : 1<C-B) (q : Fin N → ℝ) :
    rootProduct B C q≤root B C 0^N := by
  calc
    rootProduct B C q ≤ ∏ _i : Fin N, root B C 0 :=
      Finset.prod_le_prod₀ (fun i _ => (root_bounds hB hgap (q i)).1.le) (fun i _ => root_le_zero hB hgap (q i))
    _ = _ := by simp

end
end IsingBulk.Anisotropic.RegularEdges
