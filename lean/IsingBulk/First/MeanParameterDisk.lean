import IsingBulk.First.RadialDiskAdmissibility

/-! Explicit trace margin on the same fixed-radius complex parameter disks.
This exposes data already used in global admissibility, for mean deformation. -/
namespace IsingBulk.First
noncomputable section

/-- The explicit source choices are shared with radial_disk_globalRoot_admissible:
c₀=sin(theta)/4 and c₁=sin(theta)/16. The strict trace margin is exposed. -/
theorem radial_disk_source_trace_margin {theta : ℝ} (htheta : 0 < Real.sin theta) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < epsilon₀ → ∀ s : ℂ,
        ‖s-IsingBulk.Branch.radialParameter theta epsilon‖ < (Real.sin theta/16)*epsilon →
        1 < ‖s‖ ∧
        (Real.exp (-(Real.sin theta/4)*epsilon))⁻¹-Real.exp (-(Real.sin theta/4)*epsilon) <
          (sourceS s).im := by
  let c₀ : ℝ := Real.sin theta/4
  let c₁ : ℝ := Real.sin theta/16
  have hc₁ : 0 < c₁ := by dsimp [c₁]; positivity
  have hc₁small : c₁ ≤ 1/16 := by dsimp [c₁]; linarith [Real.sin_le_one theta]
  obtain ⟨epsilon₀,he0,he1,hm⟩ := radialDampingMargin_linear htheta
    (show c₀ < Real.sin theta/2 by dsimp [c₀]; linarith)
  refine ⟨epsilon₀,he0,he1,?_⟩
  intro epsilon he hel s hs
  change ‖s-IsingBulk.Branch.radialParameter theta epsilon‖ < c₁*epsilon at hs
  have he1' : epsilon ≤ 1 := hel.le.trans he1
  have hbound : c₁*epsilon ≤ 1/16 := by
    calc
      c₁*epsilon ≤ (1/16:ℝ)*epsilon := mul_le_mul_of_nonneg_right hc₁small he.le
      _ ≤ 1/16 := by linarith
  have hsn : (1:ℝ)/2 ≤ ‖s‖ := norm_ge_half_of_near_unit
    (t := IsingBulk.Branch.radialParameter theta epsilon)
    (by rw [radialParameter_norm he.le]; linarith) (by linarith)
  have htrace := sourceS_im_lower hsn
    (show 1 ≤ ‖IsingBulk.Branch.radialParameter theta epsilon‖ by rw [radialParameter_norm he.le]; linarith)
  have hcenter := radialRadius_parameter_margin he (hm epsilon he hel)
  have hsmall : 3*(c₁*epsilon) < Real.sin theta*epsilon := by
    dsimp [c₁]
    nlinarith [mul_pos htheta he]
  have hmargin : (Real.exp (-c₀*epsilon))⁻¹-Real.exp (-c₀*epsilon) < (sourceS s).im := by
    linarith
  refine ⟨?_,hmargin⟩
  have hh := norm_sub_norm_le (IsingBulk.Branch.radialParameter theta epsilon) s
  rw [norm_sub_rev, radialParameter_norm he.le] at hh
  have hc1 : c₁*epsilon < epsilon := by nlinarith
  linarith

end
end IsingBulk.First
