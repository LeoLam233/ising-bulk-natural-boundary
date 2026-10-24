import IsingBulk.First.ShapePeriodTheorem

/-! Actual constrained Vandermonde periods for the complex anisotropic
quadratic coefficient. This proves the period is nonzero, not the separate
identification with the singular asymptotic of the complete coefficient. -/
namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First

theorem shapePeriod_rightHalfPlane_eq_beta {n k : ℕ} (hn : 1 ≤ n)
    (hdegree : n-1+(n+1)*n = 2*k) {Q : ℝ} (hQ : 0 < Q)
    {c : ℂ} (hc : 0 < c.re) :
    shapePeriod n k Q c = (shapeAngularConstant n : ℂ)/2 * (Q : ℂ)^(-1/2 : ℂ) *
      c^(-(k : ℂ)-1/2) * Complex.betaIntegral ((k : ℂ)+1/2) (1/2) := by
  rw [shapePeriod_eq_radial hn hdegree]
  rw [shapeRadialIntegral_eq_value_of_positive k hQ
    (fun d hd => shapeRadialIntegral_positive_beta k hQ hd) hc]
  simp only [Complex.real_smul, shapeRadialValue]
  ring

theorem shapePeriod_rightHalfPlane_ne_zero {n k : ℕ} (hn : 1 ≤ n)
    (hdegree : n-1+(n+1)*n = 2*k) {Q : ℝ} (hQ : 0 < Q)
    {c : ℂ} (hc : 0 < c.re) : shapePeriod n k Q c ≠ 0 := by
  rw [shapePeriod_eq_radial hn hdegree]
  rw [shapeRadialIntegral_eq_value_of_positive k hQ
    (fun d hd => shapeRadialIntegral_positive_beta k hQ hd) hc]
  apply smul_ne_zero (shapeAngularConstant_pos hn).ne'
  apply shapeRadialValue_ne_zero k hQ
  intro hz
  simp [hz] at hc

/-- The regular edge coefficient -iB/sin θ belongs to the open right half
plane, not just the imaginary-axis case used in the isotropic source. -/
theorem edge_quadratic_re_pos {B : ℂ} (hB : 0 < B.im) {s : ℝ} (hs : 0 < s) :
    0 < (-Complex.I*B/(s : ℂ)).re := by
  simpa [Complex.div_ofReal_re,Complex.mul_re] using div_pos hB hs

/-- All positive even particle orders. The input is the actual complex
anisotropy B, with its edge condition Im B>0, and the positive sine factor. -/
theorem even_edge_shapePeriod_ne_zero {n : ℕ} (hn : 1 ≤ n) (he : Even (n+1))
    {B : ℂ} (hB : 0 < B.im) {Q s : ℝ} (hQ : 0 < Q) (hs : 0 < s) :
    shapePeriod n ((n+1)^2/2-1) Q (-Complex.I*B/(s : ℂ)) ≠ 0 :=
  shapePeriod_rightHalfPlane_ne_zero hn (source_shape_radial_exponent hn he)
    hQ (edge_quadratic_re_pos hB hs)
end
end IsingBulk.Anisotropic.RegularEdges
