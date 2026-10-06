import IsingBulk.First.ActualDensityAnalytic

/-! Actual parameter-independent bounds for the coincidence-safe numerator.
These are consequences of its proved local regularity, not model assumptions. -/
namespace IsingBulk.First
noncomputable section
open Complex Filter
open scoped BigOperators Topology

theorem actualSincFactor_nonneg {n : ℕ} (t : Fin n → ℝ) : 0 ≤ actualSincFactor t := by
  unfold actualSincFactor
  exact Finset.prod_nonneg (fun _ _ => sq_nonneg _)

theorem actualSincFactor_le_one {n : ℕ} (t : Fin n → ℝ) : actualSincFactor t ≤ 1 := by
  unfold actualSincFactor
  apply Finset.prod_le_one₀
  · intro p _
    exact sq_nonneg _
  · intro p _
    have h := Real.abs_sinc_le_one ((shapeExtend t p.1-shapeExtend t p.2)/2)
    have hh := abs_le.mp h
    nlinarith

theorem actualSincFactor_norm_le_one {n : ℕ} (t : Fin n → ℝ) : ‖(actualSincFactor t:ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (actualSincFactor_nonneg t)]
  exact actualSincFactor_le_one t

def realShapeEmbedding (n : ℕ) (p : ℂ × (Fin n → ℝ)) : ℂ × (Fin (n+1) → ℂ) :=
  (p.1,fun j => ((shapeExtend p.2 j:ℝ):ℂ))

theorem realShapeEmbedding_continuous (n : ℕ) : Continuous (realShapeEmbedding n) := by
  apply Continuous.prodMk continuous_fst
  apply continuous_pi
  intro j
  exact Complex.continuous_ofReal.comp ((continuous_shapeExtend_eval j).comp continuous_snd)

@[simp] theorem realShapeEmbedding_center (n : ℕ) (s : ℂ) :
    realShapeEmbedding n (s,0) = (s,0) := by
  simp only [realShapeEmbedding, shapeExtend_zero_exact, Pi.zero_apply, ofReal_zero]
  rfl

theorem actualRegularFactor_continuousAt_center (a : OrderedChartData) (n : ℕ) :
    ContinuousAt (fun p : ℂ × (Fin n → ℝ) => actualRegularFactor p.1 a.alpha p.2)
      (exp ((a.theta:ℂ)*I),0) := by
  have h := (complexDensityRegular_analyticAt a (n+1)).continuousAt
  rw [← realShapeEmbedding_center n (exp ((a.theta:ℂ)*I))] at h
  exact h.comp (realShapeEmbedding_continuous n).continuousAt

theorem actualRegularFactor_locally_bounded (a : OrderedChartData) (n : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ p : ℂ × (Fin n → ℝ) in 𝓝 (exp ((a.theta:ℂ)*I),0),
      ‖actualRegularFactor p.1 a.alpha p.2‖ ≤ M := by
  let M := ‖actualRegularFactor (exp ((a.theta:ℂ)*I)) a.alpha (0 : Fin n → ℝ)‖+1
  refine ⟨M, by dsimp [M]; positivity, ?_⟩
  exact ((actualRegularFactor_continuousAt_center a n).norm.tendsto.eventually
    (eventually_lt_nhds (show ‖actualRegularFactor (exp ((a.theta:ℂ)*I)) a.alpha (0 : Fin n → ℝ)‖ < M by
      dsimp [M]; linarith))).mono (fun _ h => h.le)

end
end IsingBulk.First
