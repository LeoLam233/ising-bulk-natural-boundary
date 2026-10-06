import IsingBulk.First.MeanSmallRectangle

/-! Actual continuity of the full source density on the undeformed real mean
segment. The positive radial gap is retained until after mean integration. -/
namespace IsingBulk.First
noncomputable section
open Complex Set
open scoped Topology

theorem meanProductY_real_norm (N : ℕ) (rho alpha v : ℝ) :
    ‖meanProductY N rho alpha (v:ℂ)‖ = Real.exp ((N:ℝ)*rho) := by
  rw [meanProductY,Complex.norm_exp]
  simp [Complex.mul_re]

theorem meanProductY_real_ne_one {n : ℕ} (rho alpha v : ℝ) (hrho : rho < 0) :
    1-meanProductY (n+1) rho alpha (v:ℂ) ≠ 0 := by
  have hn : ‖meanProductY (n+1) rho alpha (v:ℂ)‖ < 1 := by
    rw [meanProductY_real_norm,Real.exp_lt_one_iff]
    exact mul_neg_of_pos_of_neg (by positivity) hrho
  intro he
  have he' := congrArg norm (sub_eq_zero.mp he)
  simp only [norm_one] at he'
  linarith

theorem meanLocalDensity_real_continuousAt {n : ℕ} (s : ℂ) (rho alpha v : ℝ)
    (t : Fin n → ℝ) (hrho : rho < 0)
    (hr : ∀ j, 0 < (IsingBulk.Jets.chartW s rho alpha (((shapeExtend t j:ℝ):ℂ)+(v:ℂ)/(n+1))).re)
    (hi : ∀ j, 0 < (IsingBulk.Jets.chartW s rho alpha (((shapeExtend t j:ℝ):ℂ)+(v:ℂ)/(n+1))).im)
    (ha : ∀ j, -(Real.pi/2) < (meanChartExponent rho alpha t (v:ℂ) j).im ∧
      (meanChartExponent rho alpha t (v:ℂ) j).im < 0) :
    ContinuousAt (fun x : ℝ => meanLocalDensity s rho alpha t (x:ℂ)) v := by
  have hn := meanLocalNumerator_differentiableAt s rho alpha t (v:ℂ) hr hi
    (fun i j _ => meanChartY_pair_denominator_ne_zero rho alpha t (v:ℂ) ha i j)
  have hd := (meanProductY_hasDerivAt (n+1) rho alpha (v:ℂ)).differentiableAt.const_sub 1
  have hf := (hn.div hd (meanProductY_real_ne_one rho alpha v hrho)).continuousAt
  have he : meanLocalDensity s rho alpha t =
      (fun z => meanLocalNumerator s rho alpha t z/(1-meanProductY (n+1) rho alpha z)) :=
    funext (meanLocalDensity_eq_Y_quotient s rho alpha t)
  rw [he]
  exact hf.comp (f := fun x : ℝ => (x:ℂ)) Complex.continuous_ofReal.continuousAt

theorem parameter_real_mean_continuous (a : OrderedChartData) (n : ℕ) :
    ∃ R : ℝ, 0 < R ∧ ∀ (s : ℂ) (rho : ℝ) (t : Fin n → ℝ),
      ‖s-exp ((a.theta:ℂ)*I)‖ < R → |rho| < R → rho < 0 →
      (Real.exp rho)⁻¹-Real.exp rho < (sourceS s).im →
      (∀ j, |shapeExtend t j| < R/4) →
      ContinuousOn (fun x : ℝ => meanLocalDensity s rho a.alpha t (x:ℂ)) (Icc (-R/4) (R/4)) := by
  obtain ⟨R,hR,hD⟩ := parameterDeformedW_uniform_domain a
  refine ⟨R,hR,?_⟩
  intro s rho t hs hrho hrhoneg hmargin ht v hv
  have hN : (1:ℝ) ≤ n+1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hNp : (0:ℝ) < n+1 := by positivity
  have hq : |v/(n+1:ℝ)| ≤ R/4 := by
    rw [abs_div,abs_of_pos hNp]
    apply (div_le_iff₀ hNp).mpr
    have hv' : |v| ≤ R/4 := abs_le.mpr ⟨by linarith [hv.1],hv.2⟩
    nlinarith [mul_le_mul_of_nonneg_left hN (show 0 ≤ R/4 by positivity)]
  have hpoint (j : Fin (n+1)) := hD s rho (shapeExtend t j+v/(n+1:ℝ)) 0
    hs hrho hrhoneg
    (by have hj := ht j; have htri := abs_add_le (shapeExtend t j) (v/(n+1:ℝ)); linarith)
    (le_refl 0) hR hmargin
  apply (meanLocalDensity_real_continuousAt s rho a.alpha v t hrhoneg ?_ ?_ ?_).continuousWithinAt
  · intro j
    rw [meanChartW_eq_parameterDeformed]
    simpa using (hpoint j).1
  · intro j
    rw [meanChartW_eq_parameterDeformed]
    simpa using (hpoint j).2.1
  · intro j
    rw [meanChartExponent_im]
    simpa only [Complex.ofReal_re,add_assoc] using (hpoint j).2.2

end
end IsingBulk.First
