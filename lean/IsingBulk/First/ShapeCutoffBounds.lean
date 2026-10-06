import IsingBulk.First.ShapeCutoffLimit
import IsingBulk.First.ShapeLowerOrderBounds

/-! Parameter-independent lower-pole bounds with the same fixed shape cutoff
as the leading dominated limit. -/
namespace IsingBulk.First
noncomputable section
open MeasureTheory Set Filter Metric

theorem shape_cutoff_lower_bound {n k j : ℕ} (hn : 1 ≤ n)
    (hdegree : n-1+(n+1)*n = 2*k) (hj : j < k)
    (A D chi : ShapeSpace n → ℂ) (R : ℝ) {M c : ℝ} (hM : 0 ≤ M) (hc : 0 < c)
    (hchi : Continuous chi) (hchib : ∀ x, ‖chi x‖ ≤ 1)
    (hchis : ∀ x, chi x ≠ 0 → ‖x‖ < R)
    (hAcont : ContinuousOn A (ball 0 R)) (hDcont : ContinuousOn D (ball 0 R))
    (hAbound : ∀ x ∈ ball 0 R, ‖A x‖ ≤ M)
    (hDbound : ∀ x ∈ ball 0 R, c*‖x‖^2 ≤ ‖D x‖) :
    Integrable (fun x => (shapeVandermondeSq x:ℂ)*chi x*A x/(D x)^(j+1)) ∧
    ‖∫ x : ShapeSpace n, (shapeVandermondeSq x:ℂ)*chi x*A x/(D x)^(j+1)‖ ≤
      (M/c^(j+1))*∫ x : ShapeSpace n in ball 0 R,
        shapeVandermondeSq x/‖x‖^(2*(j+1)) := by
  classical
  let AA := (ball 0 R).piecewise (fun x => chi x*A x) (fun _ => 0)
  let DD := (ball 0 R).piecewise D (fun _ => 1)
  have hAm : Measurable AA := (hchi.continuousOn.mul hAcont).measurable_piecewise
    continuous_const.continuousOn measurableSet_ball
  have hDm : Measurable DD := hDcont.measurable_piecewise continuous_const.continuousOn measurableSet_ball
  have hAb (x : ShapeSpace n) : ‖AA x‖ ≤ M := by
    by_cases hx : x ∈ ball 0 R
    · simp only [AA, piecewise_eq_of_mem _ _ _ hx, norm_mul]
      calc
        ‖chi x‖*‖A x‖ ≤ 1*M := mul_le_mul (hchib x) (hAbound x hx) (norm_nonneg _) (by positivity)
        _ = M := one_mul _
    · simpa only [AA, piecewise_eq_of_notMem _ _ _ hx, norm_zero] using hM
  have hDb (x : ShapeSpace n) (hx : AA x ≠ 0) : c*‖x‖^2 ≤ ‖DD x‖ := by
    have hmem : x ∈ ball 0 R := by
      by_contra hh
      exact hx (piecewise_eq_of_notMem _ _ _ hh)
    simpa only [DD, piecewise_eq_of_mem _ _ _ hmem] using hDbound x hmem
  have h := localShapeQuotient_lower_bound hn hdegree hj R hM hc AA DD hAm hDm hAb hDb
  have hz (x : ShapeSpace n) (hx : x ∉ ball 0 R) : localShapeQuotient j AA DD x = 0 := by
    simp only [localShapeQuotient, AA, piecewise_eq_of_notMem _ _ _ hx, mul_zero, zero_div]
  have hInd : (ball 0 R).indicator (localShapeQuotient j AA DD) = localShapeQuotient j AA DD := by
    funext x
    by_cases hx : x ∈ ball 0 R
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx, hz x hx]
  have hi : Integrable (localShapeQuotient j AA DD) := by
    have hh := h.1.integrable_indicator measurableSet_ball
    rwa [hInd] at hh
  have heq : localShapeQuotient j AA DD =
      fun x => (shapeVandermondeSq x:ℂ)*chi x*A x/(D x)^(j+1) := by
    funext x
    by_cases hx : x ∈ ball 0 R
    · simp only [localShapeQuotient, AA, DD, piecewise_eq_of_mem _ _ _ hx]
      ring
    · have hchi0 : chi x = 0 := by
        by_contra hh
        exact hx (by simpa only [mem_ball, dist_zero_right] using hchis x hh)
      simp only [hz x hx, hchi0, mul_zero, zero_mul, zero_div]
  rw [← heq]
  refine ⟨hi,?_⟩
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  exact h.2


theorem localShapeQuotient_integrable_positive_gap {n k : ℕ} (hn : 1 ≤ n)
    (hdegree : n-1+(n+1)*n = 2*k) (A D : ShapeSpace n → ℂ)
    {epsilon M c : ℝ} (he : 0 < epsilon) (hM : 0 ≤ M) (hc : 0 < c)
    (hAm : Measurable A) (hDm : Measurable D) (hA : ∀ x, ‖A x‖ ≤ M)
    (hD : ∀ x, A x ≠ 0 → c*(epsilon+‖x‖^2) ≤ ‖D x‖) :
    Integrable (localShapeQuotient k A D) := by
  let c' := c*min epsilon 1
  have hc' : 0 < c' := mul_pos hc (lt_min he zero_lt_one)
  have hi := (shapeMajorant_integrable hn hdegree).const_mul (M/(c'^(k+1)))
  have hm : Measurable (localShapeQuotient k A D) :=
    ((Complex.continuous_ofReal.measurable.comp (shapeVandermondeSq_continuous n).measurable).mul hAm).div
      (hDm.pow_const _)
  apply hi.mono' hm.aestronglyMeasurable
  apply Eventually.of_forall
  intro x
  by_cases hx : A x = 0
  · simp only [localShapeQuotient, hx, mul_zero, zero_div, norm_zero]
    exact mul_nonneg (div_nonneg hM (pow_nonneg hc'.le _))
      (div_nonneg (shapeVandermondeSq_nonneg x) (by positivity))
  · apply norm_shapeQuotient_le hM hc' x (A x) (D x) (hA x)
    have hd := hD x hx
    have hmin : min epsilon 1*(1+‖x‖^2) ≤ epsilon+‖x‖^2 := by
      have h1 := min_le_left epsilon (1:ℝ)
      have h2 := min_le_right epsilon (1:ℝ)
      nlinarith [sq_nonneg ‖x‖]
    calc
      c'*(1+‖x‖^2) = c*(min epsilon 1*(1+‖x‖^2)) := by dsimp [c']; ring
      _ ≤ c*(epsilon+‖x‖^2) := mul_le_mul_of_nonneg_left hmin hc.le
      _ ≤ ‖D x‖ := hd

theorem shape_cutoff_integrable_positive_gap {n k : ℕ} (hn : 1 ≤ n)
    (hdegree : n-1+(n+1)*n = 2*k) (A D chi : ShapeSpace n → ℂ)
    (R : ℝ) {epsilon M c : ℝ} (he : 0 < epsilon) (hM : 0 ≤ M) (hc : 0 < c)
    (hchi : Continuous chi) (hchib : ∀ x, ‖chi x‖ ≤ 1)
    (hchis : ∀ x, chi x ≠ 0 → ‖x‖ < R)
    (hAcont : ContinuousOn A (ball 0 R)) (hDcont : ContinuousOn D (ball 0 R))
    (hAbound : ∀ x ∈ ball 0 R, ‖A x‖ ≤ M)
    (hDbound : ∀ x ∈ ball 0 R, c*(epsilon+‖x‖^2) ≤ ‖D x‖) :
    Integrable (fun x => (shapeVandermondeSq x:ℂ)*chi x*A x/(D x)^(k+1)) := by
  classical
  let AA := (ball 0 R).piecewise (fun x => chi x*A x) (fun _ => 0)
  let DD := (ball 0 R).piecewise D (fun _ => 1)
  have hAm : Measurable AA := (hchi.continuousOn.mul hAcont).measurable_piecewise
    continuous_const.continuousOn measurableSet_ball
  have hDm : Measurable DD := hDcont.measurable_piecewise continuous_const.continuousOn measurableSet_ball
  have hAb (x : ShapeSpace n) : ‖AA x‖ ≤ M := by
    by_cases hx : x ∈ ball 0 R
    · simp only [AA, piecewise_eq_of_mem _ _ _ hx, norm_mul]
      calc
        ‖chi x‖*‖A x‖ ≤ 1*M := mul_le_mul (hchib x) (hAbound x hx) (norm_nonneg _) (by positivity)
        _ = M := one_mul _
    · simpa only [AA, piecewise_eq_of_notMem _ _ _ hx, norm_zero] using hM
  have hDb (x : ShapeSpace n) (hx : AA x ≠ 0) : c*(epsilon+‖x‖^2) ≤ ‖DD x‖ := by
    have hmem : x ∈ ball 0 R := by
      by_contra hh
      exact hx (piecewise_eq_of_notMem _ _ _ hh)
    simpa only [DD, piecewise_eq_of_mem _ _ _ hmem] using hDbound x hmem
  have hi := localShapeQuotient_integrable_positive_gap hn hdegree AA DD he hM hc hAm hDm hAb hDb
  convert hi using 1
  funext x
  by_cases hx : x ∈ ball 0 R
  · simp only [localShapeQuotient, AA, DD, piecewise_eq_of_mem _ _ _ hx]
    ring
  · have hchi0 : chi x = 0 := by
      by_contra hh
      exact hx (by simpa only [mem_ball, dist_zero_right] using hchis x hh)
    simp only [localShapeQuotient, AA, piecewise_eq_of_notMem _ _ _ hx, hchi0,
      mul_zero, zero_mul, zero_div]

end
end IsingBulk.First
