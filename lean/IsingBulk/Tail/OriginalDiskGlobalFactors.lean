import IsingBulk.Tail.OriginalGlobalDisk

/-! Uniform global factors on the actual original c ε parameter disk. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch

theorem original_disk_trace_margin (θ c : ℝ) (hθ : 0 < Real.sin θ)
    (hc : 0 < c) (hcsmall : c < Real.sin θ/2) :
    ∃ δ ε₀ : ℝ, 0 < δ ∧ δ ≤ 1/16 ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ s : ℂ,
      ‖s-radialParameter θ ε‖ ≤ δ*ε →
      Real.exp (c*ε)-Real.exp (-c*ε) < (sourceS s).im := by
  let δ := Real.sin θ/16
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδsmall : δ ≤ 1/16 := by dsimp [δ]; linarith [Real.sin_le_one θ]
  obtain ⟨ε₀,hε₀,hε₁,hm⟩ := radialDampingMargin_linear hθ hcsmall
  refine ⟨δ,ε₀,hδ,hδsmall,hε₀,hε₁,?_⟩
  intro ε hε he s hs
  have he1 : ε ≤ 1 := he.le.trans hε₁
  have ht : 1 ≤ ‖radialParameter θ ε‖ := by rw [radialParameter_norm hε.le]; linarith
  have hsn : 1/2 ≤ ‖s‖ := norm_ge_half_of_near_unit ht (by nlinarith)
  have htrace := sourceS_im_lower hsn ht
  have hcenter := radialRadius_parameter_margin hε (hm ε hε he)
  have hgap : (Real.exp (-c*ε))⁻¹-Real.exp (-c*ε) < (sourceS s).im := by
    have hδeq : δ=Real.sin θ/16 := rfl
    nlinarith [mul_pos hθ hε]
  simpa only [neg_mul,Real.exp_neg,inv_inv] using hgap

theorem original_disk_inverse_root_bound (θ c δ ε : ℝ) (hc : 0 < c)
    (hcsmall : c ≤ 1/2) (hδ : δ ≤ 1/16) (hε : 0 < ε) (he : ε ≤ 1)
    (s y : ℂ) (hs : ‖s-radialParameter θ ε‖ ≤ δ*ε)
    (hy : ‖y‖=Real.exp (-c*ε))
    (hm : Real.exp (c*ε)-Real.exp (-c*ε) < (sourceS s).im) :
    ‖(globalRoot s y)⁻¹‖ ≤ 12+Real.exp 1 := by
  have ht : 1 ≤ ‖radialParameter θ ε‖ := by rw [radialParameter_norm hε.le]; linarith
  have hsn : 1/2 ≤ ‖s‖ := norm_ge_half_of_near_unit ht (by nlinarith)
  have hs3 : ‖s‖ ≤ 3 := by
    have hh := norm_le_norm_add_norm_sub (radialParameter θ ε) s
    rw [radialParameter_norm hε.le,norm_sub_rev] at hh
    nlinarith
  have hsi : ‖s⁻¹‖ ≤ 2 := by rw [norm_inv]; exact (inv_le_comm₀ (by positivity) (by norm_num)).mpr (by simpa using hsn)
  have hS : ‖sourceS s‖ ≤ 5 := (norm_add_le s s⁻¹).trans (by linarith)
  have hyr : ‖y‖ ≤ 1 := by rw [hy]; apply Real.exp_le_one_iff.mpr; nlinarith
  have hyi : ‖y⁻¹‖ ≤ Real.exp 1 := by
    rw [norm_inv,hy,neg_mul,Real.exp_neg,inv_inv]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hW : ‖sourceW s y‖ ≤ 5+(1+Real.exp 1)/2 := by
    unfold sourceW
    have hh := norm_sub_le (sourceS s) ((y+y⁻¹)/2)
    have hh2 := norm_add_le y y⁻¹
    rw [norm_div] at hh
    norm_num at hh
    linarith
  have hi : 0 < (sourceW s y).im := sourceW_upper_of_margin (Real.exp_pos _)
    (by rw [Real.exp_lt_one_iff]; nlinarith) (by simpa only [neg_mul,Real.exp_neg,inv_inv] using hm) hy
  have hz := interiorRoot_norm_lt_one hi
  have ht := interiorRoot_trace (sourceW s y)
  have heq : (globalRoot s y)⁻¹=2*sourceW s y-globalRoot s y := by
    change (interiorRoot (sourceW s y))⁻¹=2*sourceW s y-interiorRoot (sourceW s y)
    linear_combination ht
  rw [heq]
  have hh := norm_sub_le (2*sourceW s y) (globalRoot s y)
  rw [norm_mul] at hh
  norm_num at hh
  change ‖globalRoot s y‖ < 1 at hz
  linarith

theorem original_radius_inverse_gap_bound (c ε : ℝ) (hc : 0 < c) (hcsmall : c ≤ 1/2)
    (hε : 0 < ε) (he : ε ≤ 1) :
    (1-Real.exp (-2*c*ε))⁻¹^2 ≤ (Real.exp 1/(2*c))^2*ε⁻¹^2 := by
  have hx : 0 < 2*c*ε := by positivity
  have hx1 : 2*c*ε ≤ 1 := by nlinarith
  have hg : 0 < 1-Real.exp (-2*c*ε) := by
    have hh := Real.exp_lt_one_iff.mpr (show -2*c*ε < 0 by nlinarith)
    linarith
  have hl : (2*c*ε)/Real.exp 1 ≤ 1-Real.exp (-2*c*ε) := by
    have hh := Real.add_one_le_exp (2*c*ε)
    have hp : 0 < Real.exp (2*c*ε) := Real.exp_pos _
    have hlow : (2*c*ε)/Real.exp (2*c*ε) ≤ 1-Real.exp (-2*c*ε) := by
      rw [show -2*c*ε=-(2*c*ε) by ring,Real.exp_neg]
      apply (div_le_iff₀ hp).mpr
      field_simp
      linarith
    exact (div_le_div_of_nonneg_left hx.le hp (Real.exp_le_exp.mpr hx1)).trans hlow
  have hb : (1-Real.exp (-2*c*ε))⁻¹ ≤ Real.exp 1/(2*c*ε) := by
    have hh := one_div_le_one_div_of_le (by positivity : 0 < (2*c*ε)/Real.exp 1) hl
    simpa only [one_div,inv_div] using hh
  calc
    _ ≤ (Real.exp 1/(2*c*ε))^2 := pow_le_pow_left₀ (inv_nonneg.mpr hg.le) hb 2
    _ = _ := by ring

 theorem original_disk_global_factors (θ c : ℝ) (hθ : 0 < Real.sin θ)
    (hc : 0 < c) (hcsmall : c < Real.sin θ/2) :
    ∃ δ ε₀ A B : ℝ, 0 < δ ∧ 0 < ε₀ ∧ 0 < A ∧ 0 < B ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ s : ℂ,
      ‖s-radialParameter θ ε‖ ≤ δ*ε →
      Real.exp (c*ε)-Real.exp (-c*ε) < (sourceS s).im ∧
      (∀ y : ℂ, ‖y‖=Real.exp (-c*ε) → ‖(globalRoot s y)⁻¹‖ ≤ A) ∧
      (1-Real.exp (-2*c*ε))⁻¹^2 ≤ B*ε⁻¹^2 := by
  obtain ⟨δ,ε₀,hδ,hδs,hε₀,hε₁,hm⟩ := original_disk_trace_margin θ c hθ hc hcsmall
  refine ⟨δ,ε₀,12+Real.exp 1,(Real.exp 1/(2*c))^2,hδ,hε₀,by positivity,by positivity,?_⟩
  intro ε hε he s hs
  have hc1 : c ≤ 1/2 := by linarith [Real.sin_le_one θ]
  have he1 : ε ≤ 1 := he.le.trans hε₁
  have hmargin := hm ε hε he s hs
  exact ⟨hmargin,fun y hy => original_disk_inverse_root_bound θ c δ ε hc hc1 hδs hε he1
    s y hs hy hmargin, original_radius_inverse_gap_bound c ε hc hc1 hε he1⟩

end
end IsingBulk.Tail
