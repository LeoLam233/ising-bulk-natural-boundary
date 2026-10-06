import IsingBulk.First.MeanRectangle

/-! Translation of the explicitly oriented rectangle to the physical pole
v=-i*N*c0*epsilon and its actual denominator derivative -i. -/
namespace IsingBulk.First
noncomputable section
open Complex MeasureTheory Set intervalIntegral

theorem clockwiseRectangle_const_mul (delta top bottom : ℝ) (c : ℂ) (f : ℂ → ℂ) :
    clockwiseRectangle delta top bottom (fun z => c*f z) =
      c*clockwiseRectangle delta top bottom f := by
  unfold clockwiseRectangle
  simp only [intervalIntegral.integral_const_mul]
  ring

/-- Purely vertical translation preserves the four specified orientations. -/
theorem clockwiseRectangle_vertical_translate (delta top bottom h : ℝ) (f : ℂ → ℂ) :
    clockwiseRectangle delta top bottom (fun z => f (z+(h:ℂ)*I)) =
      clockwiseRectangle delta (top+h) (bottom+h) f := by
  have hor (a x : ℝ) : (x:ℂ)+(a:ℂ)*I+(h:ℂ)*I = (x:ℂ)+((a+h:ℝ):ℂ)*I := by
    push_cast
    ring
  have ver (a : ℂ) :
      (∫ y : ℝ in top..bottom, f (a+(y:ℂ)*I+(h:ℂ)*I)) =
        ∫ y : ℝ in top+h..bottom+h, f (a+(y:ℂ)*I) := by
    have he (y : ℝ) : a+(y:ℂ)*I+(h:ℂ)*I = a+((y+h:ℝ):ℂ)*I := by
      push_cast
      ring
    simp_rw [he]
    exact intervalIntegral.integral_comp_add_right (fun y : ℝ => f (a+(y:ℂ)*I)) h
  have ht : (∫ x : ℝ in -delta..delta, f ((x:ℂ)+(top:ℂ)*I+(h:ℂ)*I)) =
      ∫ x : ℝ in -delta..delta, f ((x:ℂ)+((top+h:ℝ):ℂ)*I) := by simp_rw [hor]
  have hb : (∫ x : ℝ in -delta..delta, f ((x:ℂ)+(bottom:ℂ)*I+(h:ℂ)*I)) =
      ∫ x : ℝ in -delta..delta, f ((x:ℂ)+((bottom+h:ℝ):ℂ)*I) := by simp_rw [hor]
  unfold clockwiseRectangle
  rw [ht, hb, ver (delta:ℂ), ver (-(delta:ℂ))]

/-- Actual position v=-ia lies inside the physical downward rectangle. -/
theorem clockwiseRectangle_physical_inv (delta height a : ℝ)
    (hd : 0 < delta) (ha : 0 < a) (hah : a < height) :
    clockwiseRectangle delta 0 (-height) (fun v => (v+(a:ℂ)*I)⁻¹) =
      -2*(Real.pi:ℂ)*I := by
  rw [clockwiseRectangle_vertical_translate]
  apply clockwiseRectangle_inv delta (0+a) (-height+a) hd (by simpa using ha)
  linarith

/-- The positive 2*pi is derived from the actual downward contour and the
literal linear principal denominator (-i)*(v+ia). It is not an orientation input. -/
theorem clockwiseRectangle_physical_principal (delta height a : ℝ)
    (hd : 0 < delta) (ha : 0 < a) (hah : a < height) :
    clockwiseRectangle delta 0 (-height) (fun v => ((-I)*(v+(a:ℂ)*I))⁻¹) =
      2*(Real.pi:ℂ) := by
  have he : (fun v : ℂ => ((-I)*(v+(a:ℂ)*I))⁻¹) =
      (fun v => I*(v+(a:ℂ)*I)⁻¹) := by
    funext v
    simp [mul_inv_rev, mul_comm]
  rw [he, clockwiseRectangle_const_mul, clockwiseRectangle_physical_inv delta height a hd ha hah]
  ring_nf
  simp [I_sq]

end
end IsingBulk.First
