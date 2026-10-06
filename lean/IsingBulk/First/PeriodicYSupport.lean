import IsingBulk.First.PeriodicYCutoff

/-! The periodic cutoff's actual torus support and pointwise range. -/
namespace IsingBulk.First
noncomputable section
open Complex Set Filter
open scoped Topology BigOperators

theorem periodicAngle_exp (u : ℝ) : exp ((periodicAngle u:ℂ)*I) = exp ((u:ℂ)*I) := by
  have hr : (log (exp ((u:ℂ)*I))).re = 0 := by
    rw [Complex.log_re, Complex.norm_exp_ofReal_mul_I, Real.log_one]
  have hl : log (exp ((u:ℂ)*I)) = (periodicAngle u:ℂ)*I := by
    apply Complex.ext <;> simp [periodicAngle,hr]
  rw [← hl, Complex.exp_log (Complex.exp_ne_zero _)]

theorem angularChartGate_mem_Icc {N : ℕ} (alpha : ℝ) (theta : Fin N → ℝ) :
    0 ≤ angularChartGate alpha theta ∧ angularChartGate alpha theta ≤ 1 := by
  exact ⟨Finset.prod_nonneg (fun j _ => angularGate_nonneg _),
    Finset.prod_le_one₀ (fun j _ => angularGate_nonneg _) (fun j _ => angularGate_le_one _)⟩

theorem fixedYChartWeight_mem_Icc {n : ℕ} (alpha : ℝ)
    {chi : (Fin n → ℝ) → ℝ} {eta : ℝ → ℝ}
    (hc : ∀ t, 0 ≤ chi t ∧ chi t ≤ 1) (he : ∀ v, 0 ≤ eta v ∧ eta v ≤ 1)
    (theta : Fin (n+1) → ℝ) :
    0 ≤ fixedYChartWeight alpha chi eta theta ∧ fixedYChartWeight alpha chi eta theta ≤ 1 := by
  have hg := angularChartGate_mem_Icc alpha theta
  have hχ := hc (fun j => shapeCoordinates (angularChartVector alpha theta) j.castSucc)
  have hη := he (meanCoordinate (angularChartVector alpha theta))
  unfold fixedYChartWeight
  constructor
  · exact mul_nonneg (mul_nonneg hg.1 hχ.1) hη.1
  · have hp : angularChartGate alpha theta *
        chi (fun j => shapeCoordinates (angularChartVector alpha theta) j.castSucc) ≤ 1 :=
      (mul_le_mul_of_nonneg_right hg.2 hχ.1).trans (by simpa using hχ.2)
    exact (mul_le_mul_of_nonneg_right hp hη.1).trans (by simpa using hη.2)

theorem fixedYChartWeight_small_angle {n : ℕ} (alpha : ℝ)
    {chi : (Fin n → ℝ) → ℝ} {eta : ℝ → ℝ} {H delta : ℝ}
    (hchi : ∀ t, chi t ≠ 0 → ∀ j, |shapeExtend t j| < H)
    (heta : ∀ v, eta v ≠ 0 → |v| < delta)
    {theta : Fin (n+1) → ℝ} (hw : fixedYChartWeight alpha chi eta theta ≠ 0)
    (j : Fin (n+1)) : |periodicAngle (theta j+alpha)| < H+delta := by
  have hc0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hw).1).2
  have he0 := (mul_ne_zero_iff.mp hw).2
  let u := angularChartVector alpha theta
  let t : Fin n → ℝ := fun i => shapeCoordinates u i.castSucc
  have hc := hchi t hc0 j
  have he := heta (meanCoordinate u) he0
  have hN : (n+1:ℝ) ≠ 0 := by positivity
  have hj : u j = shapeExtend t j+meanCoordinate u/(n+1) := by
    exact (congrArg (fun z => z j) (meanShapeChart_coordinates hN u)).symm
  change |u j| < H+delta
  rw [hj]
  have hd : |meanCoordinate u/(n+1)| ≤ |meanCoordinate u| := by
    rw [abs_div, abs_of_pos (show (0:ℝ)<n+1 by positivity)]
    exact div_le_self (abs_nonneg _) (by have h := Nat.cast_nonneg (α := ℝ) n; linarith)
  exact lt_of_le_of_lt (abs_add_le _ _) (by linarith)

theorem circle_distance_from_chart (theta alpha : ℝ) :
    ‖exp ((theta:ℂ)*I)-exp (-(alpha:ℂ)*I)‖ =
      ‖exp ((periodicAngle (theta+alpha):ℂ)*I)-1‖ := by
  have he : exp (((theta+alpha:ℝ):ℂ)*I)*exp (-(alpha:ℂ)*I) = exp ((theta:ℂ)*I) := by
    rw [← exp_add]
    congr 1
    push_cast
    ring
  have hd : exp ((theta:ℂ)*I)-exp (-(alpha:ℂ)*I) =
      (exp (((theta+alpha:ℝ):ℂ)*I)-1)*exp (-(alpha:ℂ)*I) := by rw [← he]; ring
  rw [hd,norm_mul]
  have hn : ‖exp (-(alpha:ℂ)*I)‖ = 1 := by simpa using norm_exp_ofReal_mul_I (-alpha)
  rw [hn,mul_one,periodicAngle_exp]

theorem fixedYChartWeight_support_circle {n : ℕ} (alpha : ℝ)
    {chi : (Fin n → ℝ) → ℝ} {eta : ℝ → ℝ} {H delta : ℝ}
    (hsmall : H+delta ≤ 1)
    (hchi : ∀ t, chi t ≠ 0 → ∀ j, |shapeExtend t j| < H)
    (heta : ∀ v, eta v ≠ 0 → |v| < delta)
    {theta : Fin (n+1) → ℝ} (hw : fixedYChartWeight alpha chi eta theta ≠ 0)
    (j : Fin (n+1)) :
    ‖exp ((theta j:ℂ)*I)-exp (-(alpha:ℂ)*I)‖ < 2*(H+delta) := by
  have hu := fixedYChartWeight_small_angle alpha hchi heta hw j
  rw [circle_distance_from_chart]
  have hn : ‖(periodicAngle (theta j+alpha):ℂ)*I‖ = |periodicAngle (theta j+alpha)| := by simp
  have hb := Complex.norm_exp_sub_one_le (x := (periodicAngle (theta j+alpha):ℂ)*I)
    (by rw [hn]; exact hu.le.trans hsmall)
  rw [hn] at hb
  exact lt_of_le_of_lt hb (by linarith)

end
end IsingBulk.First
