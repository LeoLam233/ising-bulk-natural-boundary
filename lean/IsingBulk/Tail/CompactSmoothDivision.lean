import IsingBulk.Tail.SelectorParameterIntegral
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace IsingBulk.Tail
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff
universe u
variable {E G : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

def compactParameterDerivative (F : E × ℝ → G) (p : E × ℝ) : E →L[ℝ] G :=
  (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ E ℝ)

omit [FiniteDimensional ℝ E] [CompleteSpace G] in
lemma compactParameterDerivative_contDiff (F : E × ℝ → G) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (compactParameterDerivative F) := by
  exact (hF.fderiv_right (by simp)).clm_comp contDiff_const

omit [FiniteDimensional ℝ E] [CompleteSpace G] in
lemma compactParameterDerivative_hasFDerivAt (F : E × ℝ → G) (hF : ContDiff ℝ ∞ F)
    (x : E) (t : ℝ) :
    HasFDerivAt (fun y => F (y,t)) (compactParameterDerivative F (x,t)) x := by
  exact ((hF.differentiable (by simp)) (x,t)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).prodMk (hasFDerivAt_const t x))

omit [CompleteSpace G] in
lemma compact_parameter_integral_hasFDerivAt (F : E × ℝ → G) (hF : ContDiff ℝ ∞ F)
    (x : E) : HasFDerivAt (fun y => ∫ t in (0:ℝ)..1, F (y,t))
      (∫ t in (0:ℝ)..1, compactParameterDerivative F (x,t)) x := by
  have hD := (compactParameterDerivative_contDiff F hF).continuous
  obtain ⟨C,hC⟩ := ((isCompact_closedBall x 1).prod (isCompact_Icc (a := (0:ℝ)) (b := 1))).exists_bound_of_continuousOn hD.continuousOn
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := closedBall x 1) (bound := fun _ => C) (closedBall_mem_nhds x (by norm_num))
  · exact Filter.Eventually.of_forall (fun y =>
      (hF.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
  · exact (hF.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1
  · exact (hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [] with t ht y hy
    exact hC (y,t) ⟨hy,by simpa using Ioc_subset_Icc_self ht⟩
  · exact intervalIntegrable_const
  · filter_upwards [] with t ht y hy
    exact compactParameterDerivative_hasFDerivAt F hF y t

lemma compact_parameter_integral_contDiff_nat (n : ℕ) (F : E × ℝ → G)
    (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ n (fun y => ∫ t in (0:ℝ)..1, F (y,t)) := by
  induction n generalizing G with
  | zero =>
    apply contDiff_zero.mpr
    exact continuous_iff_continuousAt.mpr (fun x =>
      (compact_parameter_integral_hasFDerivAt F hF x).continuousAt)
  | succ n ih =>
    apply contDiff_succ_iff_hasFDerivAt.mpr
    exact ⟨_,ih (compactParameterDerivative F) (compactParameterDerivative_contDiff F hF),
      compact_parameter_integral_hasFDerivAt F hF⟩

 theorem compact_parameter_integral_contDiff (F : E × ℝ → G) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun y => ∫ t in (0:ℝ)..1, F (y,t)) := by
  exact contDiff_infty.mpr (fun n => compact_parameter_integral_contDiff_nat n F hF)

section Division
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

def diagonalLine (z : (ℝ × ℝ) × P) (t : ℝ) : (ℝ × ℝ) × P :=
  ((z.1.2+t*(z.1.1-z.1.2),z.1.2),z.2)

def smoothDividedDifference (D : (ℝ × ℝ) × P → ℂ) (z : (ℝ × ℝ) × P) : ℂ :=
  ∫ t in (0:ℝ)..1, fderiv ℝ D (diagonalLine z t) ((1,0),0)

omit [FiniteDimensional ℝ P] in
lemma diagonalLine_contDiff : ContDiff ℝ ∞
    (fun q : ((ℝ × ℝ) × P) × ℝ => diagonalLine q.1 q.2) := by
  unfold diagonalLine
  fun_prop

lemma smoothDividedDifference_contDiff (D : (ℝ × ℝ) × P → ℂ)
    (hD : ContDiff ℝ ∞ D) : ContDiff ℝ ∞ (smoothDividedDifference D) := by
  unfold smoothDividedDifference
  apply compact_parameter_integral_contDiff (fun q => fderiv ℝ D (diagonalLine q.1 q.2) ((1,0),0))
  exact ((hD.fderiv_right (by simp)).comp diagonalLine_contDiff).clm_apply contDiff_const

omit [FiniteDimensional ℝ P] in
lemma smoothDividedDifference_identity (D : (ℝ × ℝ) × P → ℂ)
    (hD : ContDiff ℝ ∞ D) (z : (ℝ × ℝ) × P) :
    D z - D ((z.1.2,z.1.2),z.2) =
      (z.1.1-z.1.2 : ℝ) • smoothDividedDifference D z := by
  have hd (t : ℝ) : HasDerivAt (fun t => D (diagonalLine z t))
      ((z.1.1-z.1.2 : ℝ) • fderiv ℝ D (diagonalLine z t) ((1,0),0)) t := by
    have hl : HasDerivAt (diagonalLine z)
        (((z.1.1-z.1.2),0),0) t := by
      unfold diagonalLine
      simpa using
        ((((hasDerivAt_id t).mul_const (z.1.1-z.1.2)).const_add z.1.2).prodMk
          (hasDerivAt_const t z.1.2)).prodMk (hasDerivAt_const t z.2)
    have hc := ((hD.differentiable (by simp)) (diagonalLine z t)).hasFDerivAt.comp_hasDerivAt t hl
    have he : (((z.1.1-z.1.2),0),0) = (z.1.1-z.1.2 : ℝ) • (((1,0),0) : (ℝ × ℝ) × P) := by simp
    rw [he, map_smul] at hc
    exact hc
  have hc : Continuous (fun t => (z.1.1-z.1.2 : ℝ) •
      fderiv ℝ D (diagonalLine z t) ((1,0),0)) := by
    have hline : Continuous (diagonalLine z) := by unfold diagonalLine; fun_prop
    exact (((hD.continuous_fderiv (by simp)).comp hline).clm_apply
      (continuous_const (y := (((1,0),0) : (ℝ × ℝ) × P)))).const_smul (z.1.1-z.1.2 : ℝ)

  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hd t) (hc.intervalIntegrable 0 1)
  simpa [diagonalLine,smoothDividedDifference,intervalIntegral.integral_smul] using he.symm

lemma smooth_hadamard_division (D : (ℝ × ℝ) × P → ℂ)
    (hD : ContDiff ℝ ∞ D) (hdiag : ∀ y p, D ((y,y),p)=0) :
    ∃ C : (ℝ × ℝ) × P → ℂ, ContDiff ℝ ∞ C ∧
      ∀ z, D z = (z.1.1-z.1.2 : ℝ) • C z := by
  refine ⟨smoothDividedDifference D,smoothDividedDifference_contDiff D hD,?_⟩
  intro z
  simpa [hdiag] using smoothDividedDifference_identity D hD z

end Division

end
end IsingBulk.Tail
