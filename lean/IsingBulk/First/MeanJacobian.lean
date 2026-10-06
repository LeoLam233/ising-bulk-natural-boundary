import IsingBulk.First.MeanCoordinates

/-! Exact determinant of the source mean-first coordinate map. -/
namespace IsingBulk.First
noncomputable section
open scoped BigOperators

/-- Columns are ordered (v,t₁,...,tₙ), as in the manuscript. -/
def meanChartMatrix (n : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  fun i => Fin.cons ((n+1 : ℝ)⁻¹)
    (fun j => if i = j.castSucc then 1 else if i = Fin.last n then -1 else 0)

@[simp] theorem meanChartMatrix_zero (n : ℕ) (i : Fin (n+1)) :
    meanChartMatrix n i 0 = (n+1 : ℝ)⁻¹ := by simp [meanChartMatrix]

@[simp] theorem meanChartMatrix_succ (n : ℕ) (i : Fin (n+1)) (j : Fin n) :
    meanChartMatrix n i j.succ =
      if i = j.castSucc then 1 else if i = Fin.last n then -1 else 0 := by
  simp [meanChartMatrix]

theorem sum_meanChartMatrix (n : ℕ) (j : Fin (n+1)) :
    ∑ i, meanChartMatrix n i j = if j = 0 then 1 else 0 := by
  refine Fin.cases ?_ (fun k => ?_) j
  · simp only [meanChartMatrix_zero, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ite_true]
    push_cast
    exact mul_inv_cancel₀ (by positivity)
  · simp only [meanChartMatrix_succ, Fin.succ_ne_zero, ite_false]
    rw [Fin.sum_univ_castSucc]
    simp [Ne.symm (Fin.castSucc_ne_last k)]

/-- Replacing the last row by the sum of all rows makes it (1,0,...,0). -/
def meanChartRowReduced (n : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  (meanChartMatrix n).updateRow (Fin.last n) (fun j => if j=0 then 1 else 0)

theorem meanChartRowReduced_det (n : ℕ) :
    (meanChartRowReduced n).det = (meanChartMatrix n).det := by
  have h := Matrix.det_updateRow_sum (meanChartMatrix n) (Fin.last n) (fun _ => (1:ℝ))
  have he : (∑ k, (1:ℝ) • meanChartMatrix n k) = (fun j => if j=0 then 1 else 0) := by
    funext j
    simp only [one_smul]
    calc
      (∑ k, meanChartMatrix n k) j = ∑ k, meanChartMatrix n k j :=
        Finset.sum_apply j Finset.univ _
      _ = _ := sum_meanChartMatrix n j
  rw [he] at h
  simpa only [one_smul, meanChartRowReduced] using h

theorem meanChartRowReduced_minor (n : ℕ) :
    (meanChartRowReduced n).submatrix (Fin.last n).succAbove (0 : Fin (n+1)).succAbove =
      (1 : Matrix (Fin n) (Fin n) ℝ) := by
  ext i j
  simp [meanChartRowReduced, Matrix.submatrix_apply, Matrix.updateRow_apply, Matrix.one_apply]

theorem meanChartMatrix_det (n : ℕ) : (meanChartMatrix n).det = (-1:ℝ)^n := by
  rw [← meanChartRowReduced_det, Matrix.det_succ_row _ (Fin.last n)]
  have hrow (j : Fin (n+1)) :
      meanChartRowReduced n (Fin.last n) j = if j=0 then 1 else 0 := by
    simp only [meanChartRowReduced, Matrix.updateRow_self]
  simp_rw [hrow]
  rw [Finset.sum_eq_single (0 : Fin (n+1))]
  · have hm := meanChartRowReduced_minor n
    simp only [Fin.succAbove_last, Fin.succAbove_zero] at hm
    simp [hm]
  · intro j _ hj
    simp [hj]
  · simp

theorem meanChartMatrix_abs_det (n : ℕ) : |(meanChartMatrix n).det| = 1 := by
  rw [meanChartMatrix_det, abs_pow]
  simp

/-- The determinant matrix acts on exactly the inverse source chart, rather
than on an unrelated linear model. -/
theorem meanChartMatrix_mulVec (n : ℕ) (v : ℝ) (t : Fin n → ℝ) :
    (meanChartMatrix n).mulVec (Fin.cons v t) = meanShapeChart v t := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.cons_zero,
    Fin.cons_succ, meanChartMatrix_zero, meanChartMatrix_succ, meanShapeChart]
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [shapeExtend_last, Fin.ext_iff, Fin.val_last, Fin.val_castSucc]
    have hne (j : Fin n) : ¬n = (j:ℕ) := ne_of_gt j.isLt
    simp only [hne, ite_false, ite_true, neg_one_mul, Finset.sum_neg_distrib]
    ring
  · simp only [Fin.castSucc_inj, Fin.castSucc_ne_last, ite_false, shapeExtend_castSucc]
    simp
    ring

end
end IsingBulk.First
