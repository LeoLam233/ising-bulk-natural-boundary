import IsingBulk.First.MeanParameterRectangle

/-! The physical mean rectangle can be chosen below any preceding threshold. -/
namespace IsingBulk.First
noncomputable section
open Complex IsingBulk.Branch Set

theorem parameter_actual_mean_small_rectangle (a : OrderedChartData) (n : ℕ)
    (halpha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I) = 1) :
    ∃ R : ℝ, 0 < R ∧ R ≤ Real.pi ∧ ∀ (delta : ℝ), 0 < delta → delta ≤ R/4 →
      ∀ (s : ℂ) (rho : ℝ) (t : Fin n → ℝ),
      ‖s-exp ((a.theta:ℂ)*I)‖ < R → |rho| < R → rho < 0 → -(n+1:ℝ)*rho < delta →
      (Real.exp rho)⁻¹-Real.exp rho < (sourceS s).im → (∀ j, |shapeExtend t j| < R/4) →
      clockwiseRectangle delta 0 (-delta) (meanLocalDensity s rho a.alpha t) = postMeanDensity s a.alpha t := by
  obtain ⟨r,hr,hD⟩ := parameterDeformedW_uniform_domain a
  let R := min r Real.pi
  have hR : 0 < R := lt_min hr Real.pi_pos
  have hRr : R ≤ r := min_le_left _ _
  have hRpi : R ≤ Real.pi := min_le_right _ _
  refine ⟨R,hR,hRpi,?_⟩
  intro delta hdelta hdeltaR s rho t hs hrho hrhoneg hheight hmargin ht
  let aa : ℝ := -(n+1:ℝ)*rho
  let p : ℂ := physicalMeanPole (n+1) rho
  have haa : 0 < aa := by dsimp [aa]; nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hp_re : p.re = 0 := by simp [p,physicalMeanPole]
  have hp_im : p.im = -aa := by simp [p,physicalMeanPole,aa]
  have hN : (1:ℝ) ≤ n+1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hNp : (0:ℝ) < n+1 := by positivity
  have hgeom (w : ℂ) (hw : w ∈ rectangleSet delta aa (-delta+aa)) :
      (∀ j, 0 < (IsingBulk.Jets.chartW s rho a.alpha (((shapeExtend t j:ℝ):ℂ)+(p+w)/(n+1))).re) ∧
      (∀ j, 0 < (IsingBulk.Jets.chartW s rho a.alpha (((shapeExtend t j:ℝ):ℂ)+(p+w)/(n+1))).im) ∧
      (∀ j, -(Real.pi/2) < (meanChartExponent rho a.alpha t (p+w) j).im ∧
        (meanChartExponent rho a.alpha t (p+w) j).im < 0) := by
    have hxr := hw.1
    have hyi := hw.2
    rw [uIcc_of_le (by linarith)] at hxr
    rw [uIcc_of_ge (by linarith)] at hyi
    have hvre : |(p+w).re| ≤ delta := by
      simp only [Complex.add_re,hp_re,zero_add]
      exact abs_le.mpr hxr
    have hvlo : -delta ≤ (p+w).im := by rw [Complex.add_im,hp_im]; linarith [hyi.1]
    have hvhi : (p+w).im ≤ 0 := by rw [Complex.add_im,hp_im]; linarith [hyi.2]
    have hq : |(p+w).re/(n+1:ℝ)| ≤ delta := by
      rw [abs_div,abs_of_pos hNp]
      apply (div_le_iff₀ hNp).mpr
      nlinarith [mul_le_mul_of_nonneg_left hN (show 0 ≤ delta by positivity)]
    have hdepth : 0 ≤ -(p+w).im/(n+1:ℝ) := div_nonneg (by linarith) hNp.le
    have hdepth' : -(p+w).im/(n+1:ℝ) < r := by
      have hle : -(p+w).im/(n+1:ℝ) ≤ delta := by
        apply (div_le_iff₀ hNp).mpr
        nlinarith [mul_le_mul_of_nonneg_left hN (show 0 ≤ delta by positivity)]
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
      (rectangleSet delta aa (-delta+aa)) := by
    apply meanLocalNumerator_shift_differentiableOn
    · intro w hw j
      exact (hgeom w hw).1 j
    · intro w hw j
      exact (hgeom w hw).2.1 j
    · intro w hw j
      exact (hgeom w hw).2.2 j
  have hres := actual_mean_rectangle_residue s rho a.alpha delta delta t halpha
    (by positivity) (by linarith [Real.pi_pos]) haa hheight hf
  calc
    _ = 2*(Real.pi:ℂ)*meanLocalNumerator s rho a.alpha t p := hres
    _ = _ := postMeanDensity_eq_physical_residue s rho a.alpha t halpha

end
end IsingBulk.First
