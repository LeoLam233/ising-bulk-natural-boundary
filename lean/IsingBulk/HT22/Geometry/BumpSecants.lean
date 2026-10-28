import IsingBulk.Preferred22.CoordinateScale

namespace IsingBulk.HT22.Geometry
noncomputable section
open scoped Topology
open Set IsingBulk.Preferred22

theorem actual_bump_secant_error (d : PreferredBranchData) (B : PreferredCoareaBump d) :
    ∃ K : ℝ, 0<K ∧ ∀ τ σ υ x y : ℝ,
      0≤τ → σ∈Icc 0 1 → υ∈Icc 0 1 → x∈Icc (-Real.pi) Real.pi →
      y∈Icc (-Real.pi) Real.pi → x≤y →
      ‖preferredBumpAngle B.m B.p τ σ υ y-preferredBumpAngle B.m B.p τ σ υ x-
        ((y-x):ℝ)‖ ≤ (2*K*τ)*(y-x) := by
  obtain ⟨K,hK,hder⟩ := preferred_bump_first_derivative_bound d B
  refine ⟨K,hK,?_⟩
  intro τ σ υ x y hτ hσ hυ hx hy hxy
  have hp := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z (_ : z∈Icc (-Real.pi) Real.pi) => (contDiff_infty_iff_deriv.mp B.smooth).1 z)
    (fun z hz => by simpa only [Real.norm_eq_abs] using (hder z hz).1)
    (convex_Icc (-Real.pi) Real.pi) hx hy
  have hm := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z (_ : z∈Icc (-Real.pi) Real.pi) => (contDiff_infty_iff_deriv.mp B.m_smooth).1 z)
    (fun z hz => by simpa only [Real.norm_eq_abs] using (hder z hz).2)
    (convex_Icc (-Real.pi) Real.pi) hx hy
  have hp' : |B.p y-B.p x|≤K*(y-x) := by
    simpa only [Real.norm_eq_abs,abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr hxy)] using hp
  have hm' : |B.m y-B.m x|≤K*(y-x) := by
    simpa only [Real.norm_eq_abs,abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr hxy)] using hm
  have heq : preferredBumpAngle B.m B.p τ σ υ y-preferredBumpAngle B.m B.p τ σ υ x-
      ((y-x):ℝ) = -Complex.I*(τ:ℂ)*((σ*(B.m y-B.m x)-υ*(B.p y-B.p x):ℝ):ℂ) := by
    unfold preferredBumpAngle
    push_cast
    ring
  rw [heq,norm_mul,norm_mul,norm_neg,Complex.norm_I,one_mul,Complex.norm_real,
    Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hτ]
  have hsum : |σ*(B.m y-B.m x)-υ*(B.p y-B.p x)| ≤
      |σ*(B.m y-B.m x)|+|υ*(B.p y-B.p x)| := abs_sub _ _
  rw [abs_mul,abs_mul,abs_of_nonneg hσ.1,abs_of_nonneg hυ.1] at hsum
  have hm1 := mul_le_mul_of_nonneg_right hσ.2 (abs_nonneg (B.m y-B.m x))
  have hp1 := mul_le_mul_of_nonneg_right hυ.2 (abs_nonneg (B.p y-B.p x))
  have hbound : |σ*(B.m y-B.m x)-υ*(B.p y-B.p x)| ≤ 2*K*(y-x) := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hbound hτ
  nlinarith

end
end IsingBulk.HT22.Geometry
