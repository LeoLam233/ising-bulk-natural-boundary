import IsingBulk.First.MeanMotion
import IsingBulk.First.MeanShapeDensity

/-! A uniformly chosen physical mean rectangle for the actual source density.
The numerator regularity and exclusion of every other pole are instantiated. -/
namespace IsingBulk.First
noncomputable section
open Complex IsingBulk.Branch Set

/-- Full physical residue identity on one fixed rectangle and fixed shape
support, with the same radial logarithmic-radius coefficient c₀. -/
theorem uniform_actual_mean_rectangle (a : OrderedChartData) (n : ℕ) (c₀ : ℝ)
    (hc : 0 < c₀) (hA : 0 < a.A₀ c₀)
    (halpha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I) = 1) :
    ∃ delta height h epsilon₀ : ℝ,
      0 < delta ∧ 0 < height ∧ 0 < h ∧ 0 < epsilon₀ ∧
      ∀ (epsilon : ℝ) (t : Fin n → ℝ),
        0 < epsilon → epsilon < epsilon₀ → (∀ j, |shapeExtend t j| < h) →
        clockwiseRectangle delta 0 (-height)
          (meanLocalDensity (radialParameter a.theta epsilon) (-c₀*epsilon) a.alpha t) =
            postMeanDensity (radialParameter a.theta epsilon) a.alpha t := by
  obtain ⟨R,hR,hRpi,hD⟩ := full_mean_rectangle_domain a c₀ hA
  let delta := R/4
  let height := R/4
  let h := R/4
  let epsilon₀ := min R (height/((n+1:ℝ)*c₀))
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hheight : 0 < height := by dsimp [height]; positivity
  have hh : 0 < h := by dsimp [h]; positivity
  have hNc : 0 < (n+1:ℝ)*c₀ := mul_pos (by positivity) hc
  have he0 : 0 < epsilon₀ := lt_min hR (div_pos hheight hNc)
  refine ⟨delta,height,h,epsilon₀,hdelta,hheight,hh,he0,?_⟩
  intro epsilon t he he0' ht
  let rho : ℝ := -c₀*epsilon
  let aa : ℝ := -(n+1:ℝ)*rho
  let p : ℂ := physicalMeanPole (n+1) rho
  have ha : 0 < aa := by dsimp [aa,rho]; nlinarith [mul_pos hNc he]
  have hah : aa < height := by
    have hep : epsilon < height/((n+1:ℝ)*c₀) := he0'.trans_le (min_le_right _ _)
    have hm := (lt_div_iff₀ hNc).mp hep
    dsimp [aa,rho]
    nlinarith
  have hp_re : p.re = 0 := by simp [p, physicalMeanPole]
  have hp_im : p.im = -aa := by simp [p, physicalMeanPole, aa]
  have hgeom (w : ℂ) (hw : w ∈ rectangleSet delta aa (-height+aa)) :
      (∀ j, 0 < (IsingBulk.Jets.chartW (radialParameter a.theta epsilon) rho a.alpha
        (((shapeExtend t j:ℝ):ℂ)+(p+w)/(n+1))).re) ∧
      (∀ j, 0 < (IsingBulk.Jets.chartW (radialParameter a.theta epsilon) rho a.alpha
        (((shapeExtend t j:ℝ):ℂ)+(p+w)/(n+1))).im) ∧
      (∀ j, -(Real.pi/2) < (meanChartExponent rho a.alpha t (p+w) j).im ∧
        (meanChartExponent rho a.alpha t (p+w) j).im < 0) := by
    have hxr := hw.1
    have hyi := hw.2
    rw [uIcc_of_le (by linarith)] at hxr
    rw [uIcc_of_ge (by linarith)] at hyi
    have hvre : |(p+w).re| ≤ R/4 := by
      simp only [Complex.add_re, hp_re, zero_add]
      exact abs_le.mpr hxr
    have hvlo : -R/4 ≤ (p+w).im := by
      rw [Complex.add_im, hp_im]
      dsimp [height] at hyi
      linarith [hyi.1]
    have hvhi : (p+w).im ≤ 0 := by rw [Complex.add_im, hp_im]; linarith [hyi.2]
    exact hD n epsilon t (p+w) he (he0'.trans_le (min_le_left _ _)) ht hvre hvlo hvhi
  have hf : DifferentiableOn ℂ
      (fun w => meanLocalNumerator (radialParameter a.theta epsilon) rho a.alpha t (p+w))
      (rectangleSet delta aa (-height+aa)) := by
    apply meanLocalNumerator_shift_differentiableOn
    · intro w hw j
      exact (hgeom w hw).1 j
    · intro w hw j
      exact (hgeom w hw).2.1 j
    · intro w hw j
      exact (hgeom w hw).2.2 j
  have hdpi : delta < 2*Real.pi := by dsimp [delta]; linarith [Real.pi_pos]
  have hres := actual_mean_rectangle_residue (radialParameter a.theta epsilon) rho a.alpha delta height t
    halpha hdelta hdpi ha hah hf
  calc
    _ = 2*(Real.pi:ℂ)*meanLocalNumerator (radialParameter a.theta epsilon) rho a.alpha t p := hres
    _ = _ := postMeanDensity_eq_physical_residue _ rho a.alpha t halpha

end
end IsingBulk.First
