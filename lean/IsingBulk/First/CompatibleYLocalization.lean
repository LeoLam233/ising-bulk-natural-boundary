import IsingBulk.First.CompatibleYCutoffData

/-! Exact relation to centered periodicization and the compact lifted local
weight, with no seam integral equality assumed. -/
namespace IsingBulk.First
noncomputable section
open Complex Set Filter Metric
open scoped Topology ContDiff BigOperators

def rawMeanShapeWeight {n : ℕ} (chi : (Fin n → ℝ) → ℝ) (eta : ℝ → ℝ)
    (u : Fin (n+1) → ℝ) : ℝ :=
  chi (fun j => shapeCoordinates u j.castSucc)*eta (meanCoordinate u)

theorem rawMeanShapeWeight_contDiff {n : ℕ} {chi : (Fin n → ℝ) → ℝ} {eta : ℝ → ℝ}
    (hc : ContDiff ℝ ∞ chi) (he : ContDiff ℝ ∞ eta) :
    ContDiff ℝ ∞ (rawMeanShapeWeight chi eta) := by
  have hs : ContDiff ℝ ∞ (fun u : Fin (n+1) → ℝ =>
      fun j : Fin n => shapeCoordinates u j.castSucc) := by
    unfold shapeCoordinates meanCoordinate
    fun_prop
  have hm : ContDiff ℝ ∞ (@meanCoordinate ℝ _ (n+1)) := by unfold meanCoordinate; fun_prop
  exact (hc.comp hs).mul (he.comp hm)

theorem rawMeanShapeWeight_support_bound {n : ℕ}
    {chi : (Fin n → ℝ) → ℝ} {eta : ℝ → ℝ} {H delta : ℝ}
    (hchi : ∀ t, chi t ≠ 0 → ∀ j, |shapeExtend t j| < H)
    (heta : ∀ v, eta v ≠ 0 → |v| < delta)
    {u : Fin (n+1) → ℝ} (hu : rawMeanShapeWeight chi eta u ≠ 0) (j : Fin (n+1)) :
    |u j| < H+delta := by
  have h := mul_ne_zero_iff.mp hu
  let t : Fin n → ℝ := fun i => shapeCoordinates u i.castSucc
  have hc := hchi t h.1 j
  have he := heta (meanCoordinate u) h.2
  have hN : (n+1:ℝ) ≠ 0 := by positivity
  have hj : u j = shapeExtend t j+meanCoordinate u/(n+1) :=
    (congrArg (fun z => z j) (meanShapeChart_coordinates hN u)).symm
  rw [hj]
  have hd : |meanCoordinate u/(n+1)| ≤ |meanCoordinate u| := by
    rw [abs_div, abs_of_pos (show (0:ℝ)<n+1 by positivity)]
    exact div_le_self (abs_nonneg _) (by have h := Nat.cast_nonneg (α := ℝ) n; linarith)
  exact lt_of_le_of_lt (abs_add_le _ _) (by linarith)

theorem rawMeanShapeWeight_hasCompactSupport {n : ℕ}
    {chi : (Fin n → ℝ) → ℝ} {eta : ℝ → ℝ} {H delta : ℝ} (hR : 0 ≤ H+delta)
    (hchi : ∀ t, chi t ≠ 0 → ∀ j, |shapeExtend t j| < H)
    (heta : ∀ v, eta v ≠ 0 → |v| < delta) : HasCompactSupport (rawMeanShapeWeight chi eta) := by
  have hs : Function.support (rawMeanShapeWeight chi eta) ⊆ closedBall 0 (H+delta) := by
    intro u hu
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hR]
    intro j
    simpa only [Real.norm_eq_abs] using (rawMeanShapeWeight_support_bound hchi heta hu j).le
  exact (isCompact_closedBall (0 : Fin (n+1) → ℝ) (H+delta)).of_isClosed_subset
    (isClosed_tsupport _) (closure_minimal hs isClosed_closedBall)

/-- The smooth gated construction is exactly the centered wrap of the compact
raw product. The gate is one on every point where that product is nonzero. -/
theorem fixedYChartWeight_eq_periodicization {n : ℕ} (alpha : ℝ)
    {chi : (Fin n → ℝ) → ℝ} {eta : ℝ → ℝ} {H delta : ℝ}
    (hsmall : H+delta ≤ 1/2)
    (hchi : ∀ t, chi t ≠ 0 → ∀ j, |shapeExtend t j| < H)
    (heta : ∀ v, eta v ≠ 0 → |v| < delta) (theta : Fin (n+1) → ℝ) :
    fixedYChartWeight alpha chi eta theta =
      rawMeanShapeWeight chi eta (fun j => periodicAngle (theta j+alpha)) := by
  by_cases hz : rawMeanShapeWeight chi eta (angularChartVector alpha theta) = 0
  · change angularChartGate alpha theta *
      chi (fun j => shapeCoordinates (angularChartVector alpha theta) j.castSucc) *
      eta (meanCoordinate (angularChartVector alpha theta)) = _
    rw [mul_assoc]
    change angularChartGate alpha theta * rawMeanShapeWeight chi eta (angularChartVector alpha theta) = _
    rw [hz,mul_zero]
    exact hz.symm
  · have hg : angularChartGate alpha theta = 1 := by
      apply Finset.prod_eq_one
      intro j _
      apply angularGate_eq_one
      have he := congrArg Complex.re (periodicAngle_exp (theta j+alpha))
      have hcos : Real.cos (theta j+alpha) = Real.cos (angularChartVector alpha theta j) := by
        simpa only [Complex.exp_ofReal_mul_I_re, angularChartVector] using he.symm
      rw [hcos]
      have hu := (rawMeanShapeWeight_support_bound hchi heta hz j).le.trans hsmall
      have hab := abs_le.mp hu
      have hh := Real.one_sub_sq_div_two_le_cos (x := angularChartVector alpha theta j)
      nlinarith
    simp only [fixedYChartWeight,hg,one_mul,rawMeanShapeWeight]
    rfl

theorem shifted_angle_eq_one {theta alpha : ℝ}
    (h : exp ((theta:ℂ)*I) = exp (-(alpha:ℂ)*I)) :
    exp (((theta+alpha:ℝ):ℂ)*I) = 1 := by
  rw [ofReal_add,add_mul,exp_add,h,← exp_add]
  simp [neg_mul]

namespace CompatibleYCutoffData
variable {n : ℕ} {alpha beta : ℝ} {U : Set (Fin n → ℝ)}

theorem raw_compact (c : CompatibleYCutoffData n alpha beta U) :
    HasCompactSupport (rawMeanShapeWeight c.chi c.eta) :=
  rawMeanShapeWeight_hasCompactSupport (by linarith [c.H_pos,c.delta_pos]) c.shape_support c.eta_support

theorem left_periodicization (c : CompatibleYCutoffData n alpha beta U) (theta : Fin (n+1) → ℝ) :
    c.leftWeight theta = rawMeanShapeWeight c.chi c.eta (fun j => periodicAngle (theta j+alpha)) :=
  fixedYChartWeight_eq_periodicization alpha c.small c.shape_support c.eta_support theta

theorem right_periodicization (c : CompatibleYCutoffData n alpha beta U) (theta : Fin (n+1) → ℝ) :
    c.rightWeight theta = rawMeanShapeWeight c.chi c.eta (fun j => periodicAngle (theta j+beta)) :=
  fixedYChartWeight_eq_periodicization beta c.small c.shape_support c.eta_support theta

theorem remainder_excludes_actual_y (c : CompatibleYCutoffData n alpha beta U)
    {theta : Fin (n+1) → ℝ}
    (hy : (∀ j, exp ((theta j:ℂ)*I)=exp (-(alpha:ℂ)*I)) ∨
      (∀ j, exp ((theta j:ℂ)*I)=exp (-(beta:ℂ)*I))) : theta ∉ tsupport c.remainder := by
  rcases hy with h | h
  · exact c.remainder_excludes_left (fun j => shifted_angle_eq_one (h j))
  · exact c.remainder_excludes_right (fun j => shifted_angle_eq_one (h j))

end CompatibleYCutoffData
end
end IsingBulk.First
