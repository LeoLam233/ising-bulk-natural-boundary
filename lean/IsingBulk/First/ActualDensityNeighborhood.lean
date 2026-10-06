import IsingBulk.First.ActualDensityBounds

/-! A genuine joint neighborhood where the physical canceled numerator and
pole denominator are analytic in s, with every original pair pole excluded. -/
namespace IsingBulk.First
noncomputable section
open Complex Filter Set
open scoped Topology

def ActualDensityDomain (a : OrderedChartData) (n : ℕ) (p : ℂ × (Fin n → ℝ)) : Prop :=
  AnalyticAt ℂ (fun s => actualRegularFactor s a.alpha p.2) p.1 ∧
  AnalyticAt ℂ (fun s => shapePoleDenominator s a.alpha p.2) p.1 ∧
  (∀ i j : Fin (n+1), 1-shapeY a.alpha p.2 i*shapeY a.alpha p.2 j ≠ 0) ∧
  (∀ i j : Fin (n+1), 1-shapeZ p.1 a.alpha p.2 i*shapeZ p.1 a.alpha p.2 j ≠ 0)

theorem actualDensityDomain_eventually (a : OrderedChartData) (n : ℕ) :
    ∀ᶠ p : ℂ × (Fin n → ℝ) in 𝓝 (exp ((a.theta:ℂ)*I),0), ActualDensityDomain a n p := by
  let c : ℂ × (Fin n → ℝ) := (exp ((a.theta:ℂ)*I),0)
  have hmap : Tendsto (realShapeEmbedding n) (𝓝 c)
      (𝓝 (exp ((a.theta:ℂ)*I),(0 : Fin (n+1) → ℂ))) := by
    simpa only [c, realShapeEmbedding_center] using (realShapeEmbedding_continuous n).continuousAt.tendsto (x := c)
  have hB := hmap.eventually (complexDensityRegular_analyticAt a (n+1)).eventually_analyticAt
  have hD := hmap.eventually (complexDensityDenominator_analyticAt a (n+1)).eventually_analyticAt
  have hY (j : Fin (n+1)) : Continuous (fun p : ℂ × (Fin n → ℝ) => shapeY a.alpha p.2 j) := by
    unfold shapeY
    fun_prop
  have hZ (j : Fin (n+1)) : ContinuousAt (fun p : ℂ × (Fin n → ℝ) => shapeZ p.1 a.alpha p.2 j) c := by
    have h := (complexDensityZ_analyticAt a (n+1) j).continuousAt
    rw [← realShapeEmbedding_center n (exp ((a.theta:ℂ)*I))] at h
    exact h.comp (realShapeEmbedding_continuous n).continuousAt
  have hy : ∀ᶠ p : ℂ × (Fin n → ℝ) in 𝓝 c,
      ∀ i j : Fin (n+1), 1-shapeY a.alpha p.2 i*shapeY a.alpha p.2 j ≠ 0 := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    apply (continuousAt_const.sub ((hY i).continuousAt.mul (hY j).continuousAt)).eventually_ne
    dsimp [c]
    rw [shapeY_zero_exact, shapeY_zero_exact, ← pow_two]
    exact one_sub_negative_angle_sq_ne_zero a.sin_alpha_pos.ne'
  have hz : ∀ᶠ p : ℂ × (Fin n → ℝ) in 𝓝 c,
      ∀ i j : Fin (n+1), 1-shapeZ p.1 a.alpha p.2 i*shapeZ p.1 a.alpha p.2 j ≠ 0 := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    apply (continuousAt_const.sub ((hZ i).mul (hZ j))).eventually_ne
    dsimp [c]
    rw [shapeZ_density_center, shapeZ_density_center, ← pow_two]
    exact one_sub_negative_angle_sq_ne_zero a.sin_beta_pos.ne'
  filter_upwards [hB,hD,hy,hz] with p hpB hpD hpY hpZ
  have hi : AnalyticAt ℂ (fun s : ℂ => (s,fun j => ((shapeExtend p.2 j:ℝ):ℂ))) p.1 :=
    analyticAt_id.prod analyticAt_const
  refine ⟨?_,?_,hpY,hpZ⟩
  · exact AnalyticAt.comp (f := fun s : ℂ => (s,fun j => ((shapeExtend p.2 j:ℝ):ℂ)))
      (g := complexDensityRegular a.alpha) hpB hi
  · exact AnalyticAt.comp (f := fun s : ℂ => (s,fun j => ((shapeExtend p.2 j:ℝ):ℂ)))
      (g := complexDensityDenominator a.alpha) hpD hi

theorem actualDensityDomain_ball (a : OrderedChartData) (n : ℕ) :
    ∃ r : ℝ, 0 < r ∧ ∀ p : ℂ × (Fin n → ℝ),
      dist p (exp ((a.theta:ℂ)*I),0) < r → ActualDensityDomain a n p := by
  obtain ⟨r,hr,h⟩ := Metric.eventually_nhds_iff.mp (actualDensityDomain_eventually a n)
  exact ⟨r,hr,fun p hp => h hp⟩

end
end IsingBulk.First
