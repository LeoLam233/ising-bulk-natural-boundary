import IsingBulk.First.ShapePeriodTheorem

/-! Exact reuse of the proper source-independent hyperplane beta-integral
calculation. This imports no natural-boundary or complete-tail endpoint.
The zero-sum hyperplane, Vandermonde, and its 1/sqrt(N) measure factor are
the actual previously proved definitions, not abstract parameters. -/
namespace IsingBulk.Preferred22
noncomputable section
open Complex MeasureTheory

def sourceCotangent (α : ℝ) : ℝ := Real.cos α / Real.sin α

theorem sourceCotangent_pos {α : ℝ} (hα : 0 < α) (hαπ : α < Real.pi / 2) :
    0 < sourceCotangent α := by
  apply div_pos
  · exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hαπ⟩
  · exact Real.sin_pos_of_pos_of_lt_pi hα (by linarith [Real.pi_pos])

def sourceShapePeriod (n : ℕ) (α : ℝ) : ℂ :=
  IsingBulk.First.shapePeriod n ((n + 1) ^ 2 / 2 - 1)
    (2 * (n + 1)) (-Complex.I * sourceCotangent α)

/-- LT22 Lemma 10.3 in its exact free-coordinate realization. -/
theorem source_shape_period {n : ℕ} (hn : 1 ≤ n) (he : Even (n + 1))
    {α : ℝ} (hα : 0 < α) (hαπ : α < Real.pi / 2) :
    let k := (n + 1) ^ 2 / 2 - 1
    let a₀ : ℂ := (((n + 1 : ℕ) : ℂ) ^ 2 - 1) / 2
    Integrable (fun t : Fin n → ℝ =>
      let x := IsingBulk.First.shapeCoordinateEquiv n (WithLp.toLp 2 t)
      (IsingBulk.First.shapeVandermondeSq x : ℂ) /
        ((2 * (n + 1) : ℝ) - Complex.I * sourceCotangent α * (‖x‖ : ℂ) ^ 2) ^ (k + 1)) ∧
    sourceShapePeriod n α =
      (IsingBulk.First.shapeAngularConstant n : ℂ) / 2 *
        ((2 * (n + 1) : ℝ) : ℂ) ^ (-1 / 2 : ℂ) *
        (-Complex.I * sourceCotangent α) ^ (-a₀) * Complex.betaIntegral a₀ (1 / 2) ∧
    sourceShapePeriod n α ≠ 0 := by
  exact IsingBulk.First.lemma_period hn he (by positivity) (sourceCotangent_pos hα hαπ)

end
end IsingBulk.Preferred22
