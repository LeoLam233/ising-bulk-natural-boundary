import IsingBulk.First.RadialAdmissibility
import IsingBulk.First.SourceParameterBounds

/-! A fixed evaluation radius on a genuine complex s-disk of size c1*epsilon.
The source parameter and every y angle share the same constants and domain. -/
namespace IsingBulk.First
noncomputable section

 theorem radialParameter_norm {θ ε : ℝ} (hε : 0 ≤ ε) :
    ‖IsingBulk.Branch.radialParameter θ ε‖ = 1+ε := by
  rw [IsingBulk.Branch.radialParameter, norm_mul,
    Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by linarith)]

/-- Every parameter in the source complex disk has the same global admissible
circle r=exp(-c0*epsilon); this is prior to differentiation. -/
theorem radial_disk_globalRoot_admissible {θ : ℝ} (hθ : 0 < Real.sin θ) :
    ∃ c₀ c₁ ε₀ : ℝ, 0 < c₀ ∧ c₀ < Real.sin θ/2 ∧ 0 < c₁ ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ s : ℂ,
        ‖s-IsingBulk.Branch.radialParameter θ ε‖ < c₁*ε →
        1 < ‖s‖ ∧ ScalarResidueAdmissible (Real.exp (-c₀*ε)) s (globalRoot s) := by
  let c₀ : ℝ := Real.sin θ/4
  let c₁ : ℝ := Real.sin θ/16
  have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
  have hc₁ : 0 < c₁ := by dsimp [c₁]; positivity
  have hc₁small : c₁ ≤ 1/16 := by dsimp [c₁]; linarith [Real.sin_le_one θ]
  obtain ⟨ε₀, hε₀, hε₁, hm⟩ := radialDampingMargin_linear hθ
    (show c₀ < Real.sin θ/2 by dsimp [c₀]; linarith)
  refine ⟨c₀, c₁, ε₀, hc₀, (by dsimp [c₀]; linarith), hc₁, hε₀, hε₁, ?_⟩
  intro ε hε hεlt s hs
  have hε1 : ε ≤ 1 := hεlt.le.trans hε₁
  have hbound : c₁*ε ≤ 1/16 := by
    calc
      c₁*ε ≤ (1/16:ℝ)*ε := mul_le_mul_of_nonneg_right hc₁small hε.le
      _ ≤ 1/16 := by linarith
  have hsn : (1:ℝ)/2 ≤ ‖s‖ := norm_ge_half_of_near_unit (t := IsingBulk.Branch.radialParameter θ ε)
    (by rw [radialParameter_norm hε.le]; linarith) (by linarith)
  have htrace := sourceS_im_lower hsn
    (show 1 ≤ ‖IsingBulk.Branch.radialParameter θ ε‖ by rw [radialParameter_norm hε.le]; linarith)
  have hcenter := radialRadius_parameter_margin hε (hm ε hε hεlt)
  have hsmall : 3*(c₁*ε) < Real.sin θ*ε := by
    dsimp [c₁]
    nlinarith [mul_pos hθ hε]
  have hmargin : (Real.exp (-c₀*ε))⁻¹-Real.exp (-c₀*ε) < (sourceS s).im := by linarith
  constructor
  · have hh := norm_sub_norm_le (IsingBulk.Branch.radialParameter θ ε) s
    rw [norm_sub_rev, radialParameter_norm hε.le] at hh
    have hc1 : c₁*ε < ε := by nlinarith
    linarith
  · exact globalRoot_admissible (Real.exp_pos _)
      (by rw [Real.exp_lt_one_iff]; nlinarith [mul_pos hc₀ hε]) hmargin

end
end IsingBulk.First
