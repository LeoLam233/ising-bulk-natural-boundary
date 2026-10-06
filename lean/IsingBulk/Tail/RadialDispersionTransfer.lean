import IsingBulk.Tail.CompactLimitingGeometry

/-! Uniform, actual-source radial dispersion transfer. Its constants do
not depend on angle, particle number or coupled occupancy. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First

def radialAnglePoint (v θ : ℝ) : ℂ := Complex.exp ((v:ℂ)+(θ:ℂ)*Complex.I)

theorem radial_trace_difference_bound (v : ℝ) (y : ℂ) (hy : ‖y‖=1) (hv : |v|≤1) :
    ‖((Complex.exp (v:ℂ)*y)+(Complex.exp (v:ℂ)*y)⁻¹)/2-(y+y⁻¹)/2‖ ≤ 2*|v| := by
  have hpos : ‖Complex.exp (v:ℂ)-1‖ ≤ 2*|v| := by
    simpa only [Complex.norm_real,Real.norm_eq_abs] using
      Complex.norm_exp_sub_one_le (x := (v:ℂ)) (by simpa using hv)
  have hneg : ‖Complex.exp (-(v:ℂ))-1‖ ≤ 2*|v| := by
    simpa only [norm_neg,Complex.norm_real,Real.norm_eq_abs] using
      Complex.norm_exp_sub_one_le (x := -(v:ℂ)) (by simpa using hv)
  have he : ((Complex.exp (v:ℂ)*y)+(Complex.exp (v:ℂ)*y)⁻¹)/2-(y+y⁻¹)/2 =
      ((Complex.exp (v:ℂ)-1)*y+(Complex.exp (-(v:ℂ))-1)*y⁻¹)/2 := by
    rw [mul_inv_rev,← Complex.exp_neg]
    ring
  rw [he,norm_div]
  have hh := norm_add_le ((Complex.exp (v:ℂ)-1)*y) ((Complex.exp (-(v:ℂ))-1)*y⁻¹)
  simp only [norm_mul,norm_inv,hy,inv_one,mul_one] at hh
  norm_num
  linarith

/-- Transfer from the actual complex s and radial angle to any fixed real
limiting trace S. No analyticity of cutoffs or occupancy constancy is needed. -/
theorem radial_sourceW_transfer (s : ℂ) (S v θ : ℝ) (hv : |v|≤1) :
    ‖sourceW s (radialAnglePoint v θ)-((S-Real.cos θ:ℝ):ℂ)‖ ≤
      ‖sourceS s-(S:ℂ)‖+2*|v| := by
  have htrace := radial_trace_difference_bound v (limitingAngle θ) (limitingAngle_norm θ) hv
  have hy : radialAnglePoint v θ=Complex.exp (v:ℂ)*limitingAngle θ := by
    exact Complex.exp_add _ _
  have ht : (limitingAngle θ+(limitingAngle θ)⁻¹)/2=(Real.cos θ:ℂ) := by
    rw [limitingAngle_trace]
    ring
  rw [← hy,ht] at htrace
  have he : sourceW s (radialAnglePoint v θ)-((S-Real.cos θ:ℝ):ℂ) =
      (sourceS s-(S:ℂ))-((radialAnglePoint v θ+(radialAnglePoint v θ)⁻¹)/2-(Real.cos θ:ℂ)) := by
    unfold sourceW
    push_cast
    ring
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith)

end
end IsingBulk.Tail
