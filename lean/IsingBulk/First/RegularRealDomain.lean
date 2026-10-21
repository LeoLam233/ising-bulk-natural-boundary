import IsingBulk.First.RegularParameterRectangle
import IsingBulk.First.MeanRealDomain

/-! Sign-independent regular phase foundation for the actual source. -/
namespace IsingBulk.First.Regular
noncomputable section
open Complex Filter Set IsingBulk.Branch
open scoped Topology BigOperators

theorem meanLocalDensity_real_continuousAt {n : ℕ} (s : ℂ) (rho alpha v : ℝ)
    (t : Fin n → ℝ) (hrho : rho < 0)
    (hi : ∀ j, 0 < (IsingBulk.Jets.chartW s rho alpha (((shapeExtend t j:ℝ):ℂ)+(v:ℂ)/(n+1))).im)
    (ha : ∀ j, -Real.pi < (meanChartExponent rho alpha t (v:ℂ) j).im ∧
      (meanChartExponent rho alpha t (v:ℂ) j).im < 0) :
    ContinuousAt (fun x : ℝ => meanLocalDensity s rho alpha t (x:ℂ)) v := by
  have hn := meanLocalNumerator_differentiableAt s rho alpha t (v:ℂ) hi
    (fun i j _ => meanChartY_pair_denominator_ne_zero rho alpha t (v:ℂ) ha i j)
  have hd := (meanProductY_hasDerivAt (n+1) rho alpha (v:ℂ)).differentiableAt.const_sub 1
  have hf := (hn.div hd (meanProductY_real_ne_one rho alpha v hrho)).continuousAt
  have he : meanLocalDensity s rho alpha t =
      (fun z => meanLocalNumerator s rho alpha t z/(1-meanProductY (n+1) rho alpha z)) :=
    funext (meanLocalDensity_eq_Y_quotient s rho alpha t)
  rw [he]
  exact hf.comp (f := fun x : ℝ => (x:ℂ)) Complex.continuous_ofReal.continuousAt

theorem parameter_real_mean_continuous (a : RegularChartData) (n : ℕ) :
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
  apply (meanLocalDensity_real_continuousAt s rho a.alpha v t hrhoneg ?_ ?_).continuousWithinAt
  · intro j
    rw [meanChartW_eq_parameterDeformed]
    simpa using (hpoint j).1
  · intro j
    rw [meanChartExponent_im]
    simpa only [Complex.ofReal_re,add_assoc] using (hpoint j).2

end
end IsingBulk.First.Regular
