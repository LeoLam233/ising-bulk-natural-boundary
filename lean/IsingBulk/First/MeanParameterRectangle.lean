import IsingBulk.First.MeanParameterDomain
import IsingBulk.First.MeanShapeDensity

/-! The actual mean identity on an open complex source-parameter domain,
with rho fixed throughout parameter differentiation. -/
namespace IsingBulk.First
noncomputable section
open Complex IsingBulk.Branch Set

theorem meanChartW_eq_parameterDeformed {n : ℕ} (a : OrderedChartData) (s : ℂ) (rho : ℝ)
    (t : Fin n → ℝ) (v : ℂ) (j : Fin (n+1)) :
    IsingBulk.Jets.chartW s rho a.alpha (((shapeExtend t j:ℝ):ℂ)+v/(n+1)) =
      parameterDeformedW a (s,rho,shapeExtend t j+v.re/(n+1:ℝ),-v.im/(n+1:ℝ)) := by
  change IsingBulk.Branch.dispersion _ (exp (meanChartExponent rho a.alpha t v j)) = _
  rw [meanChartExponent_eq_polar]
  unfold parameterDeformedW
  congr 2
  push_cast
  ring

/-- One fixed rectangle and fixed shape support apply simultaneously to all
parameters with the actual trace margin. These are source domain conditions,
not differentiability or residue conclusions supplied as hypotheses. -/
theorem parameter_actual_mean_rectangle (a : OrderedChartData) (n : ℕ)
    (halpha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I) = 1) :
    ∃ R : ℝ, 0 < R ∧ R ≤ Real.pi ∧ ∀ (s : ℂ) (rho : ℝ) (t : Fin n → ℝ),
      ‖s-exp ((a.theta:ℂ)*I)‖ < R → |rho| < R → rho < 0 → -(n+1:ℝ)*rho < R/4 →
      (Real.exp rho)⁻¹-Real.exp rho < (sourceS s).im → (∀ j, |shapeExtend t j| < R/4) →
      clockwiseRectangle (R/4) 0 (-(R/4)) (meanLocalDensity s rho a.alpha t) = postMeanDensity s a.alpha t := by
  obtain ⟨r,hr,hD⟩ := parameterDeformedW_uniform_domain a
  let R := min r Real.pi
  have hR : 0 < R := lt_min hr Real.pi_pos
  have hRr : R ≤ r := min_le_left _ _
  have hRpi : R ≤ Real.pi := min_le_right _ _
  refine ⟨R,hR,hRpi,?_⟩
  intro s rho t hs hrho hrhoneg hheight hmargin ht
  let aa : ℝ := -(n+1:ℝ)*rho
  let p : ℂ := physicalMeanPole (n+1) rho
  have haa : 0 < aa := by dsimp [aa]; nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hp_re : p.re = 0 := by simp [p,physicalMeanPole]
  have hp_im : p.im = -aa := by simp [p,physicalMeanPole,aa]
  have hN : (1:ℝ) ≤ n+1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hNp : (0:ℝ) < n+1 := by positivity
  have hgeom (w : ℂ) (hw : w ∈ rectangleSet (R/4) aa (-(R/4)+aa)) :
      (∀ j, 0 < (IsingBulk.Jets.chartW s rho a.alpha (((shapeExtend t j:ℝ):ℂ)+(p+w)/(n+1))).re) ∧
      (∀ j, 0 < (IsingBulk.Jets.chartW s rho a.alpha (((shapeExtend t j:ℝ):ℂ)+(p+w)/(n+1))).im) ∧
      (∀ j, -(Real.pi/2) < (meanChartExponent rho a.alpha t (p+w) j).im ∧
        (meanChartExponent rho a.alpha t (p+w) j).im < 0) := by
    have hxr := hw.1
    have hyi := hw.2
    rw [uIcc_of_le (by linarith)] at hxr
    rw [uIcc_of_ge (by linarith)] at hyi
    have hvre : |(p+w).re| ≤ R/4 := by
      simp only [Complex.add_re,hp_re,zero_add]
      exact abs_le.mpr hxr
    have hvlo : -R/4 ≤ (p+w).im := by rw [Complex.add_im,hp_im]; linarith [hyi.1]
    have hvhi : (p+w).im ≤ 0 := by rw [Complex.add_im,hp_im]; linarith [hyi.2]
    have hq : |(p+w).re/(n+1:ℝ)| ≤ R/4 := by
      rw [abs_div,abs_of_pos hNp]
      apply (div_le_iff₀ hNp).mpr
      nlinarith [mul_le_mul_of_nonneg_left hN (show 0 ≤ R/4 by positivity)]
    have hdepth : 0 ≤ -(p+w).im/(n+1:ℝ) := div_nonneg (by linarith) hNp.le
    have hdepth' : -(p+w).im/(n+1:ℝ) < r := by
      have hle : -(p+w).im/(n+1:ℝ) ≤ R/4 := by
        apply (div_le_iff₀ hNp).mpr
        nlinarith [mul_le_mul_of_nonneg_left hN (show 0 ≤ R/4 by positivity)]
      linarith
    have hpoint (j : Fin (n+1)) := hD s rho (shapeExtend t j+(p+w).re/(n+1:ℝ))
      (-(p+w).im/(n+1:ℝ)) (hs.trans_le hRr) (hrho.trans_le hRr) hrhoneg
      (show |shapeExtend t j+(p+w).re/(n+1:ℝ)| < r from by
        have htri := abs_add_le (shapeExtend t j) ((p+w).re/(n+1:ℝ))
        have hj := ht j
        linarith) hdepth hdepth' hmargin
    refine ⟨?_,?_,?_⟩
    · intro j
      rw [meanChartW_eq_parameterDeformed]
      exact (hpoint j).1
    · intro j
      rw [meanChartW_eq_parameterDeformed]
      exact (hpoint j).2.1
    · intro j
      rw [meanChartExponent_im]
      simpa only [add_assoc] using (hpoint j).2.2
  have hf : DifferentiableOn ℂ (fun w => meanLocalNumerator s rho a.alpha t (p+w))
      (rectangleSet (R/4) aa (-(R/4)+aa)) := by
    apply meanLocalNumerator_shift_differentiableOn
    · intro w hw j
      exact (hgeom w hw).1 j
    · intro w hw j
      exact (hgeom w hw).2.1 j
    · intro w hw j
      exact (hgeom w hw).2.2 j
  have hres := actual_mean_rectangle_residue s rho a.alpha (R/4) (R/4) t halpha
    (by positivity) (by linarith [Real.pi_pos]) haa hheight hf
  calc
    _ = 2*(Real.pi:ℂ)*meanLocalNumerator s rho a.alpha t p := hres
    _ = _ := postMeanDensity_eq_physical_residue s rho a.alpha t halpha

end
end IsingBulk.First
