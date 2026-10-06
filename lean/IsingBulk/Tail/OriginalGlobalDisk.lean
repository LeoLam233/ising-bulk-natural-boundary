import IsingBulk.Tail.RadialDispersionTransfer
import IsingBulk.First.RadialDiskAdmissibility
import IsingBulk.Analysis.BranchData

/-! Whole original-circle sheet preservation with the fixed source-small
radial constant supplied before ε. No particle-number dependence occurs. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch

theorem radialAnglePoint_norm (v θ : ℝ) : ‖radialAnglePoint v θ‖=Real.exp v := by
  rw [radialAnglePoint,Complex.norm_exp]
  simp

theorem original_disk_sourceW_upper (θ c : ℝ) (hθ : 0 < Real.sin θ)
    (hc : 0 < c) (hcsmall : c < Real.sin θ/2) :
    ∃ δ ε₀ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ s : ℂ,
      ‖s-radialParameter θ ε‖ ≤ δ*ε → ∀ a : ℝ,
      0 < (sourceW s (radialAnglePoint (-c*ε) a)).im := by
  let δ := Real.sin θ/16
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδsmall : δ ≤ 1/16 := by dsimp [δ]; linarith [Real.sin_le_one θ]
  obtain ⟨ε₀,hε₀,hε₁,hm⟩ := radialDampingMargin_linear hθ hcsmall
  refine ⟨δ,ε₀,hδ,by linarith,hε₀,hε₁,?_⟩
  intro ε hε he s hs a
  have he1 : ε ≤ 1 := he.le.trans hε₁
  have ht : 1 ≤ ‖radialParameter θ ε‖ := by rw [radialParameter_norm hε.le]; linarith
  have hsn : 1/2 ≤ ‖s‖ := norm_ge_half_of_near_unit ht (by nlinarith)
  have htrace := sourceS_im_lower hsn ht
  have hcenter := radialRadius_parameter_margin hε (hm ε hε he)
  have hgap : (Real.exp (-c*ε))⁻¹-Real.exp (-c*ε) < (sourceS s).im := by
    have hδeq : δ=Real.sin θ/16 := rfl
    nlinarith [mul_pos hθ hε]
  exact sourceW_upper_of_margin (Real.exp_pos _) (by rw [Real.exp_lt_one_iff]; nlinarith)
    hgap (radialAnglePoint_norm _ _)

theorem radialParameter_sub_zero_norm (θ ε : ℝ) (hε : 0 ≤ ε) :
    ‖radialParameter θ ε-radialParameter θ 0‖=ε := by
  have he : radialParameter θ ε-radialParameter θ 0=
      (ε:ℂ)*Complex.exp ((θ:ℂ)*Complex.I) := by
    unfold radialParameter
    push_cast
    ring
  rw [he,norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg hε]

theorem sourceS_radial_zero_branch (d : LocalBranchData) :
    sourceS (radialParameter d.theta 0)=((1+Real.cos d.thetaB:ℝ):ℂ) := by
  have he := radialTraceModel_eq d 0 (by norm_num)
  norm_num [radialTraceModel] at he
  change 2*Complex.cos (d.theta:ℂ)=sourceS (radialParameter d.theta 0) at he
  rw [← he,← Complex.ofReal_cos]
  exact_mod_cast (show 2*Real.cos d.theta=1+Real.cos d.thetaB by linarith [d.angle_relation])

/-- Explicit radial-center trace motion; no local constant is hidden in ε. -/
theorem sourceS_radial_to_boundary (d : LocalBranchData) (ε : ℝ) (hε : 0 ≤ ε) :
    ‖sourceS (radialParameter d.theta ε)-((1+Real.cos d.thetaB:ℝ):ℂ)‖ ≤ 3*ε := by
  rw [← sourceS_radial_zero_branch d]
  have ht : 1 ≤ ‖radialParameter d.theta 0‖ := by rw [radialParameter_norm (by norm_num)]; norm_num
  have hs : 1/2 ≤ ‖radialParameter d.theta ε‖ := by rw [radialParameter_norm hε]; linarith
  have hh := sourceS_sub_norm_le hs ht
  rw [radialParameter_sub_zero_norm d.theta ε hε] at hh
  exact hh

end
end IsingBulk.Tail
