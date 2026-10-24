import IsingBulk.Anisotropic.NegativeNormalForm.ComplexRadialPeriod
import IsingBulk.Anisotropic.NegativeNormalForm.ShapePeriodExact

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open MeasureTheory Set IsingBulk.First

theorem shapePeriod_complex_radial {n : ℕ} (hn : 1≤n) (j : ℕ) (tau : ℝ) (c : ℂ) :
    shapePeriod n j tau c=(shapeAngularConstant n:ℂ)*
      (∫ r in Ioi (0:ℝ), (r:ℂ)^(n-1+(n+1)*n)/((tau:ℂ)+c*(r:ℂ)^2)^(j+1)) := by
  rw [shapePeriod_eq_intrinsic]
  have h := integral_shapeVandermonde_polar hn
    (fun r => (((tau:ℂ)+c*(r:ℂ)^2)^(j+1))⁻¹)
  have hi : shapePeriodIntrinsic n j tau c=shapeSphereIntegral n •
      (∫ r in Ioi (0:ℝ), (r:ℂ)^(n-1+(n+1)*n)/((tau:ℂ)+c*(r:ℂ)^2)^(j+1)) := by
    simpa only [shapePeriodIntrinsic,Complex.real_smul,Complex.ofReal_pow,div_eq_mul_inv] using h
  rw [hi,smul_smul]
  rfl

/-- Literal complex-curvature shape period, with its exact integer h power. -/
theorem shapePeriod_complex_rescale {n a : ℕ} (hn : 1≤n) (ha : 0<a)
    (hdegree : n-1+(n+1)*n=2*a-1) (j : ℕ) (haj : a≤j)
    (tau c : ℝ) (ht : 0<tau) (hc : 0<c) (h : ℂ) (hh : 0<h.re) :
    shapePeriod n j tau (h*(c:ℂ))=h^(-(a:ℤ))*shapePeriod n j tau (c:ℂ) := by
  have hhc : 0<(h*(c:ℂ)).re := by simpa using mul_pos hh hc
  rw [shapePeriod_complex_radial hn,shapePeriod_complex_radial hn,hdegree,
    complexRadialBeta_order a j ha haj tau ht (h*(c:ℂ)) hhc,
    complexRadialBeta_order a j ha haj tau ht (c:ℂ) (by simpa using hc)]
  simp only [mul_pow,zpow_neg,zpow_natCast,div_eq_mul_inv,mul_inv_rev]
  ring

open IsingBulk.Anisotropic.NegativeDominance in
/-- This is the actual period needed by the unscaled physical Φ chart, not
an algebraic insertion of a Hessian factor into the real beta answer. -/
theorem negativeEdge_complex_period {p : ℕ} (hp : Odd p) (hp3 : 3≤p)
    (j : ℕ) (haj : alpha p≤j) (h : ℂ) (hh : 0<h.re) :
    shapePeriod (p-1) j (tau p) (h/(2*(p:ℂ)))=
      h^(-(alpha p:ℤ))*shapePeriod (p-1) j (tau p) ((1/(2*(p:ℝ)):ℝ):ℂ) := by
  have ha : 0<alpha p := by
    rw [alpha_eq_derivativeOrder]
    exact IsingBulk.HT.First.derivativeOrder_pos hp hp3
  have hdegree : (p-1)-1+(p-1+1)*(p-1)=2*alpha p-1 := by
    rw [show p-1+1=p by omega,alpha_eq_derivativeOrder]
    exact IsingBulk.HT.First.odd_shape_radial_exponent hp hp3
  have he := shapePeriod_complex_rescale (show 1≤p-1 by omega) ha hdegree j haj
    (tau p) (1/(2*(p:ℝ))) (tau_pos p (by omega)) (by positivity) h hh
  simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_mul,
    Complex.ofReal_ofNat,Complex.ofReal_natCast,one_div,Complex.ofReal_inv,div_eq_mul_inv,one_mul] using he

open IsingBulk.Anisotropic.NegativeDominance in
theorem negativeEdge_complex_period_ne_zero {p : ℕ} (hp : Odd p) (hp3 : 3≤p)
    (j : ℕ) (haj : alpha p≤j) (h : ℂ) (hh : 0<h.re) :
    shapePeriod (p-1) j (tau p) (h/(2*(p:ℂ)))≠0 := by
  rw [negativeEdge_complex_period hp hp3 j haj h hh]
  apply mul_ne_zero (zpow_ne_zero _ (by intro he; simp [he] at hh))
  have hp0 : 0<(p:ℝ) := by exact_mod_cast (show 0<p by omega)
  have ht := tau_pos p (show 0<p by omega)
  have hP : 0<factorialProduct p := by unfold factorialProduct; positivity
  rw [shapePeriod_factorial hp hp3 j haj (tau p) (1/(2*(p:ℝ))) ht (by positivity)]
  apply Complex.ofReal_ne_zero.mpr
  exact ne_of_gt (by positivity)

open IsingBulk.Anisotropic.NegativeDominance in
theorem negativeEdge_complex_period_integrable {p : ℕ} (hp : Odd p) (hp3 : 3≤p)
    (j : ℕ) (haj : alpha p≤j) (h : ℂ) (hh : 0<h.re) :
    Integrable (fun t : Fin (p-1) → ℝ =>
      let x := shapeCoordinateEquiv (p-1) (WithLp.toLp 2 t)
      (shapeVandermondeSq x:ℂ)/((tau p:ℂ)+(h/(2*(p:ℂ)))*(‖x‖:ℂ)^2)^(j+1)) := by
  exact Integrable.of_integral_ne_zero (negativeEdge_complex_period_ne_zero hp hp3 j haj h hh)

end
end IsingBulk.Anisotropic.NegativeNormalForm
