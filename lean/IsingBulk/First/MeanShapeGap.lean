import IsingBulk.First.MeanShapePhaseSum
import IsingBulk.First.MeanShapeDensity
import IsingBulk.First.MeanNonlinearBound

/-! Nonlinear post-residue denominator bound for the actual source Z product. -/
namespace IsingBulk.First
noncomputable section
open Complex IsingBulk.Branch
open scoped BigOperators

def shapePhaseDefect {n : ℕ} (a : OrderedChartData) (epsilon : ℝ) (t : Fin n → ℝ) : ℂ :=
  -I*((∑ j, radialResiduePhase a (epsilon:ℂ) ((shapeExtend t j:ℝ):ℂ))-(n+1:ℂ)*(a.beta:ℂ))

theorem shapeZ_radial_eq_phase {n : ℕ} (a : OrderedChartData) (epsilon : ℝ)
    (t : Fin n → ℝ) (j : Fin (n+1)) :
    shapeZ (radialParameter a.theta epsilon) a.alpha t j =
      exp (-I*radialResiduePhase a (epsilon:ℂ) ((shapeExtend t j:ℝ):ℂ)) := by
  have hW : sourceW (radialParameter a.theta epsilon) (shapeY a.alpha t j) =
      radialResidueW a (epsilon,shapeExtend t j) := by
    rw [radialResidueW_eq_chartW]
    simp [sourceW, sourceS, shapeY, IsingBulk.Jets.chartW, IsingBulk.Jets.angularY,
      IsingBulk.Branch.dispersion]
  unfold shapeZ phaseRoot
  rw [hW]
  rfl

theorem shapePoleDenominator_eq_exp_defect {n : ℕ} (a : OrderedChartData) (epsilon : ℝ)
    (t : Fin n → ℝ) (hbeta : exp (-(n+1:ℂ)*(a.beta:ℂ)*I) = 1) :
    shapePoleDenominator (radialParameter a.theta epsilon) a.alpha t =
      1-exp (shapePhaseDefect a epsilon t) := by
  have hprod : shapeZProduct (radialParameter a.theta epsilon) a.alpha t =
      exp (-I*∑ j, radialResiduePhase a (epsilon:ℂ) ((shapeExtend t j:ℝ):ℂ)) := by
    unfold shapeZProduct coordinateProduct
    simp_rw [shapeZ_radial_eq_phase]
    rw [← Complex.exp_sum]
    congr 1
    rw [Finset.mul_sum]
  have hback : exp (I*(n+1:ℂ)*(a.beta:ℂ)) = 1 := by
    rw [show I*(n+1:ℂ)*(a.beta:ℂ) = -(-(n+1:ℂ)*(a.beta:ℂ)*I) by ring,
      Complex.exp_neg, hbeta, inv_one]
  unfold shapePoleDenominator
  rw [hprod]
  congr 1
  unfold shapePhaseDefect
  rw [show -I*((∑ j, radialResiduePhase a (epsilon:ℂ) ((shapeExtend t j:ℝ):ℂ))-
    (n+1:ℂ)*(a.beta:ℂ)) =
    -I*(∑ j, radialResiduePhase a (epsilon:ℂ) ((shapeExtend t j:ℝ):ℂ))+I*(n+1:ℂ)*(a.beta:ℂ) by ring,
    Complex.exp_add, hback, mul_one]

theorem shapePhaseDefect_re {n : ℕ} (a : OrderedChartData) (epsilon : ℝ) (t : Fin n → ℝ) :
    (shapePhaseDefect a epsilon t).re =
      ∑ j, (radialResiduePhase a (epsilon:ℂ) ((shapeExtend t j:ℝ):ℂ)).im := by
  simp [shapePhaseDefect, Complex.mul_re, Complex.mul_im]

theorem shapePhaseDefect_im {n : ℕ} (a : OrderedChartData) (epsilon : ℝ) (t : Fin n → ℝ) :
    (shapePhaseDefect a epsilon t).im =
      (n+1:ℝ)*a.beta-∑ j, (radialResiduePhase a (epsilon:ℂ) ((shapeExtend t j:ℝ):ℂ)).re := by
  simp [shapePhaseDefect, Complex.mul_re, Complex.mul_im]

theorem shapePhaseDefect_norm {n : ℕ} (a : OrderedChartData) (epsilon : ℝ) (t : Fin n → ℝ)
    (hsmall : ∀ j, ‖radialResiduePhase a (epsilon:ℂ) ((shapeExtend t j:ℝ):ℂ)-(a.beta:ℂ)‖ ≤
      (2*(n+1:ℝ))⁻¹) : ‖shapePhaseDefect a epsilon t‖ ≤ 1/2 := by
  have he : (∑ j, radialResiduePhase a (epsilon:ℂ) ((shapeExtend t j:ℝ):ℂ))-(n+1:ℂ)*(a.beta:ℂ) =
      ∑ j, (radialResiduePhase a (epsilon:ℂ) ((shapeExtend t j:ℝ):ℂ)-(a.beta:ℂ)) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast
    rfl
  unfold shapePhaseDefect
  rw [norm_mul, norm_neg, Complex.norm_I, one_mul, he]
  apply (norm_sum_le _ _).trans
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hsmall j)
  have hc : (∑ _j : Fin (n+1), (2*(n+1:ℝ))⁻¹) = 1/2 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  rwa [hc] at hs

/-- The manuscript's nonlinear lower bound for the actual radius-free source
Z denominator. The constants are constructed before epsilon and the shape. -/
theorem actual_shape_denominator_lower_bound (a : OrderedChartData) (n : ℕ)
    (hbeta : exp (-(n+1:ℂ)*(a.beta:ℂ)*I) = 1) :
    ∃ c r : ℝ, 0 < c ∧ 0 < r ∧ ∀ (epsilon : ℝ) (t : Fin n → ℝ),
      0 < epsilon → epsilon < r → (∀ j, |shapeExtend t j| < r) →
      c*(epsilon+∑ j, (shapeExtend t j)^2) ≤
        ‖shapePoleDenominator (radialParameter a.theta epsilon) a.alpha t‖ := by
  obtain ⟨cA,rA,hcA,hrA,hA⟩ := radialResiduePhase_attenuation a
  obtain ⟨C,rS,hC,hrS,hS⟩ := radialResiduePhase_sum_separation a
  have hNp : (0:ℝ) < n+1 := by positivity
  have heta : 0 < (2*(n+1:ℝ))⁻¹ := by positivity
  obtain ⟨rP,hrP,hP⟩ := radialResiduePhase_near a heta
  let r := min rA (min rS (min rP 1))
  let A : ℝ := (n+1:ℝ)*cA
  let B : ℝ := a.d/2
  let E : ℝ := (n+1:ℝ)*C
  have hAp : 0 < A := mul_pos hNp hcA
  have hBp : 0 < B := div_pos a.d_pos (by norm_num)
  have hEp : 0 ≤ E := (mul_pos hNp hC).le
  have hrp : 0 < r := lt_min hrA (lt_min hrS (lt_min hrP (by norm_num)))
  have hrA' : r ≤ rA := min_le_left _ _
  have hrS' : r ≤ rS := (min_le_right _ _).trans (min_le_left _ _)
  have hrP' : r ≤ rP := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hr1 : r ≤ 1 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨A*B/(2*(A+B+E)),r,nonlinear_exp_gap_constant_pos hAp hBp hEp,hrp,?_⟩
  intro epsilon t he her ht
  have hnorm : ‖shapePhaseDefect a epsilon t‖ ≤ 1/2 :=
    shapePhaseDefect_norm a epsilon t (fun j =>
      (hP epsilon (shapeExtend t j) he (her.trans_le hrP') ((ht j).trans_le hrP')).le)
  have hreal : (shapePhaseDefect a epsilon t).re ≤ -A*epsilon := by
    rw [shapePhaseDefect_re]
    have hh := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
      show (radialResiduePhase a (epsilon:ℂ) ((shapeExtend t j:ℝ):ℂ)).im ≤ -cA*epsilon from by
        have hi := hA epsilon (shapeExtend t j) he (her.trans_le hrA') ((ht j).trans_le hrA')
        linarith)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
    dsimp [A]
    push_cast at hh
    nlinarith
  have hphase : B*(∑ j, (shapeExtend t j)^2)-E*epsilon^2 ≤ (shapePhaseDefect a epsilon t).im := by
    rw [shapePhaseDefect_im]
    have hh := hS (n+1) (Nat.succ_pos n) epsilon (shapeExtend t) he (her.trans_le hrS')
      (fun j => (ht j).trans_le hrS') (sum_shapeExtend t)
    simpa [B,E] using hh
  rw [shapePoleDenominator_eq_exp_defect a epsilon t hbeta]
  exact nonlinear_exp_gap hAp hBp hEp he.le (her.trans_le hr1).le hnorm hreal hphase

/-- The same physical estimate on a sufficiently small fixed Euclidean shape
ball, in the manuscript's dependent-coordinate convention. -/
theorem actual_shape_denominator_lower_bound_ball (a : OrderedChartData) (n : ℕ)
    (hbeta : exp (-(n+1:ℂ)*(a.beta:ℂ)*I) = 1) :
    ∃ c r : ℝ, 0 < c ∧ 0 < r ∧ ∀ (epsilon : ℝ) (t : Fin n → ℝ),
      0 < epsilon → epsilon < r → (∑ j, (shapeExtend t j)^2) < r^2 →
      c*(epsilon+∑ j, (shapeExtend t j)^2) ≤
        ‖shapePoleDenominator (radialParameter a.theta epsilon) a.alpha t‖ := by
  obtain ⟨c,r,hc,hr,hbound⟩ := actual_shape_denominator_lower_bound a n hbeta
  refine ⟨c,r,hc,hr,?_⟩
  intro epsilon t he her ht
  apply hbound epsilon t he her
  intro j
  have hs : (shapeExtend t j)^2 ≤ ∑ i, (shapeExtend t i)^2 :=
    Finset.single_le_sum (fun i _ => sq_nonneg _) (Finset.mem_univ j)
  have hsq := sq_abs (shapeExtend t j)
  nlinarith [abs_nonneg (shapeExtend t j)]

end
end IsingBulk.First
