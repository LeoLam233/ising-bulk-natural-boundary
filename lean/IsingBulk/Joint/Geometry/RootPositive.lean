import IsingBulk.Joint.Geometry.RootUniform
import IsingBulk.Joint.Geometry.PhysicalRegion

namespace IsingBulk.Joint
noncomputable section

/-- On the physical positive quadrant the canonical branch is the positive real root. -/
theorem canonicalRoot_real_positive {x u : ℝ} (hx : 0 < x) (hu : 0 < u)
    (hK : ((x : ℂ),(u : ℂ)) ∉ spectralSet) (q : ℝ) :
    (canonicalRoot ((x : ℂ),(u : ℂ)) (q : ℂ)).im = 0 ∧
    0 < (canonicalRoot ((x : ℂ),(u : ℂ)) (q : ℂ)).re ∧
    (canonicalRoot ((x : ℂ),(u : ℂ)) (q : ℂ)).re < 1 := by
  let K : Coupling := ((x : ℂ),(u : ℂ))
  let ρ := canonicalRoot K (q : ℂ)
  have hs := canonicalRoot_spec hK q
  have hconj : rootPolynomial K (q : ℂ) (star ρ) = 0 := by
    have hh := congrArg (starRingEnd ℂ) hs.1
    simpa only [rootPolynomial,S,T,A,K,ρ,← Complex.ofReal_sinh,← Complex.ofReal_cosh,
      ← Complex.ofReal_cos,map_add,map_sub,map_mul,map_pow,map_ofNat,map_zero,
      Complex.star_def,Complex.conj_ofReal] using hh
  have he : star ρ = ρ := canonicalRoot_unique hK q hconj (by simpa [ρ,K] using hs.2)
  have hi : ρ.im = 0 := by
    have hh := congrArg Complex.im he
    simp only [Complex.star_def,Complex.conj_im] at hh
    linarith
  have hρ : ρ = (ρ.re : ℂ) := Complex.ext (by simp) (by simp [hi])
  have hreal : Real.sinh x * ρ.re^2 -
      2*(Real.cosh x*Real.cosh u-Real.sinh u*Real.cos q)*ρ.re + Real.sinh x = 0 := by
    have hh : rootPolynomial K (q : ℂ) ρ = 0 := hs.1
    dsimp [rootPolynomial,S,T,A,K] at hh
    rw [hρ,← Complex.ofReal_sinh,← Complex.ofReal_sinh,← Complex.ofReal_cosh,
      ← Complex.ofReal_cosh,← Complex.ofReal_cos] at hh
    exact_mod_cast hh
  have hsu := Real.sinh_pos_iff.mpr hu
  have hsx := Real.sinh_pos_iff.mpr hx
  have hcu := Real.cosh_pos u
  have hlt : Real.sinh u < Real.cosh u := by
    nlinarith [Real.cosh_sq_sub_sinh_sq u]
  have hgap : 0 < Real.cosh x*Real.cosh u-Real.sinh u*Real.cos q := by
    have h₁ : Real.cosh u ≤ Real.cosh x*Real.cosh u := by
      nlinarith [Real.one_le_cosh x]
    have h₂ : Real.sinh u*Real.cos q ≤ Real.sinh u :=
      mul_le_of_le_one_right hsu.le (Real.cos_le_one q)
    linarith
  have hr : 0 < ρ.re := by
    by_contra hn
    have hle : ρ.re ≤ 0 := le_of_not_gt hn
    have h₁ := mul_nonneg hsx.le (sq_nonneg ρ.re)
    have h₂ := mul_nonpos_of_nonneg_of_nonpos hgap.le hle
    nlinarith
  have hn : ρ.re < 1 := by
    have hh : ‖ρ‖ < 1 := hs.2
    rw [hρ,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr] at hh
    exact hh
  exact ⟨hi,hr,hn⟩

end
end IsingBulk.Joint
