import IsingBulk.HT.First.OddShapePeriod

/-! F001 (10.4): the actual constrained Vandermonde integral, with its
coordinate Gram factor retained in shapeAngularConstant. This reuses the
exact integer-power primitive and polar integration, not any earlier first
singularity or natural-boundary conclusion. -/
namespace IsingBulk.HT22
noncomputable section
open IsingBulk.First IsingBulk.HT.First

/-- The integer power removes the curvature sign and the imaginary phase. -/
theorem odd_curvature_complex_power {p : ℕ} (hp : Odd p) (d : ℝ) :
    (-Complex.I*(d:ℂ))^(derivativeOrder p) = (|d|^(derivativeOrder p):ℝ) := by
  obtain ⟨m,hm⟩ := derivativeOrder_four_dvd hp
  have hi : (-Complex.I)^(derivativeOrder p)=(1:ℂ) := by
    rw [hm,pow_mul]
    norm_num
  rw [mul_pow,hi,one_mul,← Complex.ofReal_pow,curvature_power_eq_abs hp]

theorem constrained_odd_period_exact {p : ℕ} (hp : Odd p) (hp3 : 3≤p)
    {Q d : ℝ} (hQ : 0<Q) (hd : d≠0) :
    shapePeriod (p-1) (derivativeOrder p) Q (-Complex.I*d) =
      (shapeAngularConstant (p-1)/(2*(derivativeOrder p:ℝ)*Q*|d|^(derivativeOrder p)):ℝ) := by
  have hk := derivativeOrder_pos hp hp3
  obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  have hdeg : (p-1)-1+(p-1+1)*(p-1)=2*m+1 := by
    have h := odd_shape_radial_exponent hp hp3
    rw [show p-1+1=p by omega]
    omega
  have hphase := odd_curvature_complex_power hp d
  rw [hm,show Nat.succ m=m+1 by rfl] at hphase ⊢
  rw [odd_shapePeriod_eq_radial (by omega) hdeg,odd_radial_integral m hQ hd,hphase]
  push_cast
  ring

theorem constrained_odd_period_positive {p : ℕ} (hp : Odd p) (hp3 : 3≤p)
    {Q d : ℝ} (hQ : 0<Q) (hd : d≠0) :
    ∃ J : ℝ, 0<J ∧ shapePeriod (p-1) (derivativeOrder p) Q (-Complex.I*d)=(J:ℂ) := by
  refine ⟨shapeAngularConstant (p-1)/(2*(derivativeOrder p:ℝ)*Q*|d|^(derivativeOrder p)),?_,
    constrained_odd_period_exact hp hp3 hQ hd⟩
  have hS := shapeAngularConstant_pos (n := p-1) (by omega)
  have hk : 0 < (derivativeOrder p:ℝ) := by exact_mod_cast derivativeOrder_pos hp hp3
  have hdpos : 0 < |d| := abs_pos.mpr hd
  positivity

end
end IsingBulk.HT22
