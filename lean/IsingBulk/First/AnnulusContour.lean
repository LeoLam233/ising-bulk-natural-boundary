import IsingBulk.First.VariableContour

/-! Genuine one-coordinate annulus deformation and its finite product extension. -/
namespace IsingBulk.First
noncomputable section
open Set MeasureTheory Metric

theorem normalizedCircleIntegral_annulus {r R : ℝ} (hr : 0 < r) (hR : r ≤ R)
    (f : ℂ → ℂ) (hf : ∀ w : ℂ, r ≤ ‖w‖ → ‖w‖ ≤ R → DifferentiableAt ℂ f w) :
    normalizedCircleIntegral R f = normalizedCircleIntegral r f := by
  have hc : ContinuousOn f (closedBall 0 R \ ball 0 r) := by
    intro w hw
    apply (hf w ?_ ?_).continuousAt.continuousWithinAt
    · simpa only [mem_ball, dist_zero_right, not_lt] using hw.2
    · simpa only [mem_closedBall, dist_zero_right] using hw.1
  have hd : ∀ w ∈ (ball 0 R \ closedBall 0 r) \ (∅ : Set ℂ), DifferentiableAt ℂ f w := by
    intro w hw
    apply hf w
    · exact (lt_of_not_ge (by simpa only [mem_closedBall, dist_zero_right] using hw.1.2)).le
    · exact (show ‖w‖ < R by simpa only [mem_ball, dist_zero_right] using hw.1.1).le
  have hh := Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hR
    Set.countable_empty hc hd
  unfold normalizedCircleIntegral
  rw [hh]

def annularProduct (N : ℕ) (r R : ℝ) : Set (Fin N → ℂ) :=
  {x | ∀ i, r ≤ ‖x i‖ ∧ ‖x i‖ ≤ R}

theorem variableAngleTuple_mem_annularProduct {N : ℕ} {r R : ℝ} (hr : 0 < r)
    (U : Fin N → ℝ) (hU : ∀ i, r ≤ U i ∧ U i ≤ R) (θ : Fin N → ℝ) :
    variableAngleTuple U θ ∈ annularProduct N r R := by
  intro i
  change r ≤ ‖anglePoint (U i) (θ i)‖ ∧ ‖anglePoint (U i) (θ i)‖ ≤ R
  rw [anglePoint_norm (hr.trans_le (hU i).1).le]
  exact hU i

theorem variableCircleIntegrand_continuous {N : ℕ} {r R : ℝ} (hr : 0 < r)
    (f : (Fin N → ℂ) → ℂ)
    (hf : ∀ x ∈ annularProduct N r R, DifferentiableAt ℂ f x)
    (U : Fin N → ℝ) (hU : ∀ i, r ≤ U i ∧ U i ≤ R) :
    Continuous (fun θ => variableAngleJacobian U θ * f (variableAngleTuple U θ)) := by
  apply continuous_iff_continuousAt.mpr
  intro θ
  have hx := (hf _ (variableAngleTuple_mem_annularProduct hr U hU θ)).continuousAt
  exact (variableAngleJacobian_continuous U).continuousAt.mul
    (hx.comp_of_eq (variableAngleTuple_continuous U).continuousAt rfl)

theorem differentiableAt_insertNth_head {n : ℕ} (i : Fin (n+1)) (x : Fin n → ℂ) (w : ℂ) :
    DifferentiableAt ℂ (fun z : ℂ => (i.insertNth z x : Fin (n+1) → ℂ)) w := by
  apply differentiableAt_pi.mpr
  intro j
  by_cases hj : j=i
  · subst j
    simp only [Fin.insertNth_apply_same]
    convert! (differentiableAt_id (𝕜 := ℂ) (x := w)) using 1
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
    simpa only [Fin.insertNth_apply_succAbove] using differentiableAt_const (𝕜 := ℂ) (x k) (x := w)

/-- Change one radius using Cauchy on the actual annulus and genuine Fubini. -/
theorem variableCircleIntegral_update {n : ℕ} {r R : ℝ} (hr : 0 < r)
    (f : (Fin (n+1) → ℂ) → ℂ)
    (hf : ∀ x ∈ annularProduct (n+1) r R, DifferentiableAt ℂ f x)
    (U : Fin (n+1) → ℝ) (hU : ∀ i, r ≤ U i ∧ U i ≤ R)
    (i : Fin (n+1)) (q : ℝ) (hi : U i ≤ q) (hq : q ≤ R) :
    variableCircleIntegral (Function.update U i q) f = variableCircleIntegral U f := by
  have hU' : ∀ j, r ≤ Function.update U i q j ∧ Function.update U i q j ≤ R := by
    intro j
    by_cases hj : j=i
    · subst j
      simp only [Function.update_self]
      exact ⟨(hU i).1.trans hi, hq⟩
    · simpa [Function.update_of_ne hj] using hU j
  rw [variableCircleIntegral_succAbove i _ f (variableCircleIntegrand_continuous hr f hf _ hU'),
    variableCircleIntegral_succAbove i _ f (variableCircleIntegrand_continuous hr f hf _ hU)]
  have htail : (fun j => Function.update U i q (i.succAbove j)) = (fun j => U (i.succAbove j)) := by
    funext j
    exact Function.update_of_ne (i.succAbove_ne j) _ _
  rw [htail, Function.update_self]
  apply setIntegral_congr_fun measurableSet_Icc
  intro θ _
  dsimp only
  congr 1
  apply normalizedCircleIntegral_annulus (hr.trans_le (hU i).1) hi
  intro w hwlow hwhigh
  apply (hf _ ?_).comp w (differentiableAt_insertNth_head i _ w)
  intro j
  by_cases hj : j=i
  · subst j
    simp only [Fin.insertNth_apply_same]
    exact ⟨(hU i).1.trans hwlow, hwhigh.trans hq⟩
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
    simp only [Fin.insertNth_apply_succAbove, variableAngleTuple]
    rw [anglePoint_norm (hr.trans_le (hU (i.succAbove k)).1).le]
    exact hU (i.succAbove k)

end
end IsingBulk.First
