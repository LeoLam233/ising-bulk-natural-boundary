import IsingBulk.Tail.CompactSmoothDivision

namespace IsingBulk.Tail
noncomputable section
open Set
open scoped ContDiff
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

lemma smoothDividedDifference_diagonal (D : (ℝ × ℝ) × P → ℂ) (y : ℝ) (p : P) :
    smoothDividedDifference D ((y,y),p) = fderiv ℝ D ((y,y),p) ((1,0),0) := by
  simp [smoothDividedDifference,diagonalLine]

lemma smoothDividedDifference_sub_bound (D D0 : (ℝ × ℝ) × P → ℂ)
    (hD : ContDiff ℝ ∞ D) (hD0 : ContDiff ℝ ∞ D0)
    (z : (ℝ × ℝ) × P) (epsilon : ℝ)
    (hb : ∀ t ∈ Icc (0:ℝ) 1,
      ‖fderiv ℝ D (diagonalLine z t) ((1,0),0) -
        fderiv ℝ D0 (diagonalLine z t) ((1,0),0)‖ ≤ epsilon) :
    ‖smoothDividedDifference D z-smoothDividedDifference D0 z‖ ≤ epsilon := by
  have hline : Continuous (diagonalLine z) := by unfold diagonalLine; fun_prop
  have hc (F : (ℝ × ℝ) × P → ℂ) (hF : ContDiff ℝ ∞ F) :
      Continuous (fun t => fderiv ℝ F (diagonalLine z t) ((1,0),0)) :=
    ((hF.continuous_fderiv (by simp)).comp hline).clm_apply continuous_const
  unfold smoothDividedDifference
  rw [← intervalIntegral.integral_sub ((hc D hD).intervalIntegrable 0 1)
    ((hc D0 hD0).intervalIntegrable 0 1)]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := 1) (fun t ht => hb t (by simpa using Ioc_subset_Icc_self ht))
  simpa using hh

lemma smoothDividedDifference_margin (D D0 : (ℝ × ℝ) × P → ℂ)
    (hD : ContDiff ℝ ∞ D) (hD0 : ContDiff ℝ ∞ D0)
    (z : (ℝ × ℝ) × P) (epsilon c : ℝ)
    (hb : ∀ t ∈ Icc (0:ℝ) 1,
      ‖fderiv ℝ D (diagonalLine z t) ((1,0),0) -
        fderiv ℝ D0 (diagonalLine z t) ((1,0),0)‖ ≤ epsilon)
    (hbase : c ≤ ‖smoothDividedDifference D0 z‖) (he : epsilon ≤ c/2) :
    c/2 ≤ ‖smoothDividedDifference D z‖ := by
  have hh := smoothDividedDifference_sub_bound D D0 hD hD0 z epsilon hb
  have ht := norm_sub_norm_le (smoothDividedDifference D0 z) (smoothDividedDifference D z)
  rw [norm_sub_rev] at ht
  linarith

end
end IsingBulk.Tail
