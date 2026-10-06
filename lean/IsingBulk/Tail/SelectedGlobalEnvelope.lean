import IsingBulk.Tail.SelectedFContinuation
import IsingBulk.Tail.SelectedYKernel
import IsingBulk.Tail.ExteriorConvergenceBounds
import IsingBulk.First.RadialDiskAdmissibility

/-! Uniform exponential envelope for global inverse products on the selected
continued disk. No unit-disk assumption is imposed on continued compact roots. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch
open scoped BigOperators

theorem quadratic_root_norm_envelope {W z : ℂ} {M : ℝ}
    (hq : z^2-2*W*z+1=0) (hW : ‖W‖ ≤ M) : ‖z‖ ≤ 2*M+1 := by
  have hM : 0 ≤ M := (norm_nonneg W).trans hW
  by_cases hz : ‖z‖ ≤ 1
  · linarith
  have hzi : ‖z⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ (le_of_lt (lt_of_not_ge hz))
  have ht := quadratic_root_trace hq
  have he : z=2*W-z⁻¹ := by linear_combination ht
  calc
    ‖z‖ = ‖2*W-z⁻¹‖ := congrArg norm he
    _ ≤ 2*‖W‖+‖z⁻¹‖ := by simpa using norm_sub_le (2*W) z⁻¹
    _ ≤ 2*M+1 := by linarith

theorem quadratic_inverse_norm_envelope {W z : ℂ} {M : ℝ}
    (hq : z^2-2*W*z+1=0) (hW : ‖W‖ ≤ M) : ‖z⁻¹‖ ≤ 4*M+1 := by
  have h := quadratic_inverse_norm_bound hq hW (quadratic_root_norm_envelope hq hW)
  linarith

theorem selected_shift_lower {N : ℕ} (hN : 0 < N) {τ : ℝ} (hτ : 0 ≤ τ)
    (p m : Fin N → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (hm0 : ∀ i, 0 ≤ m i) (i : Fin N) :
    -2*τ ≤ retractionShift τ p m i := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have ho := occupancy_nonneg hp0
  have hc : 0 ≤ τ*occupancy p/(2*N)*m i :=
    mul_nonneg (div_nonneg (mul_nonneg hτ ho) (by positivity)) (hm0 i)
  have hpi := hp1 i
  unfold retractionShift
  nlinarith

theorem selected_y_norm_envelope {N : ℕ} (hN : 0 < N) (f : SelectorFunctions)
    {c₀ τ ε : ℝ} (hc : 0 ≤ c₀) (hτ : 0 ≤ τ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hp0 : ∀ x, 0 ≤ f.p x) (hp1 : ∀ x, f.p x ≤ 1)
    (hm0 : ∀ x, 0 ≤ f.m x) (hm1 : ∀ x, f.m x ≤ 1)
    (θ : Fin N → ℝ) (i : Fin N) :
    ‖deformedPoint f (Real.exp (-c₀*ε)) τ 1 θ i‖ ≤ Real.exp (c₀+2*τ) ∧
    ‖(deformedPoint f (Real.exp (-c₀*ε)) τ 1 θ i)⁻¹‖ ≤ Real.exp (c₀+2*τ) := by
  let h := retractionShift τ (fun j => f.p (θ j)) (fun j => f.m (θ j)) i
  have hlo : -2*τ ≤ h := selected_shift_lower hN hτ _ _ (fun j => hp0 _) (fun j => hp1 _) (fun j => hm0 _) i
  have hhi : h ≤ τ/2 := shift_le_half_tau hN hτ _ _ (fun j => hp0 _) (fun j => hp1 _) (fun j => hm0 _) (fun j => hm1 _) i
  have he : ‖deformedPoint f (Real.exp (-c₀*ε)) τ 1 θ i‖ = Real.exp (-c₀*ε+h) := by
    rw [deformedPoint_norm f (Real.exp_nonneg _)]
    simp only [one_mul,← Real.exp_add]
    rfl
  constructor
  · rw [he]
    apply Real.exp_le_exp.mpr
    nlinarith
  · rw [norm_inv,he,← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    nlinarith

theorem selected_disk_parameter_envelope {θ ε c : ℝ} {N : ℕ}
    (hN : 1 ≤ N) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hc : c ≤ 1/4)
    {s : ℂ} (hs : ‖s-radialParameter θ ε‖ ≤ c/(N:ℝ)) :
    1/2 ≤ ‖s‖ ∧ ‖s‖ ≤ 3 := by
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have hcn : c/(N:ℝ) ≤ 1/4 := by
    apply (div_le_iff₀ (by linarith : (0:ℝ)<N)).mpr
    linarith
  have hnorm := radialParameter_norm (θ := θ) hε
  have hl := norm_sub_norm_le (radialParameter θ ε) s
  rw [norm_sub_rev] at hl
  have hu := norm_sub_norm_le s (radialParameter θ ε)
  constructor <;> linarith

theorem selected_sourceW_envelope {s y : ℂ} {E : ℝ}
    (hs0 : 1/2 ≤ ‖s‖) (hs1 : ‖s‖ ≤ 3) (hy : ‖y‖ ≤ E) (hyi : ‖y⁻¹‖ ≤ E) :
    ‖sourceW s y‖ ≤ 5+E := by
  have hsi : ‖s⁻¹‖ ≤ 2 := by
    rw [norm_inv,inv_eq_one_div]
    apply (div_le_iff₀ (by linarith : (0:ℝ)<‖s‖)).mpr
    linarith
  unfold sourceW sourceS
  calc
    _ ≤ ‖s+s⁻¹‖+‖(y+y⁻¹)/2‖ := norm_sub_le _ _
    _ ≤ (‖s‖+‖s⁻¹‖)+(‖y‖+‖y⁻¹‖)/2 := by
      apply add_le_add (norm_add_le _ _)
      rw [norm_div]
      rw [show ‖(2:ℂ)‖ = (2:ℝ) by norm_num]
      exact div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
    _ ≤ 5+E := by linarith

/-- Actual selected inverse-product numerator, with a base independent of N
and epsilon. No false N-independent bound on an inverse product is used. -/
theorem selected_actual_inverse_numerator {N : ℕ} (hN : 1 ≤ N)
    (f : SelectorFunctions) {c₀ τ ε c θ₀ : ℝ} (hc₀ : 0 ≤ c₀) (hτ : 0 ≤ τ)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hc : c ≤ 1/4)
    (hp0 : ∀ x, 0 ≤ f.p x) (hp1 : ∀ x, f.p x ≤ 1)
    (hm0 : ∀ x, 0 ≤ f.m x) (hm1 : ∀ x, f.m x ≤ 1)
    (θ : Fin N → ℝ) {s : ℂ} (hs : ‖s-radialParameter θ₀ ε‖ ≤ c/(N:ℝ)) :
    let y := deformedPoint f (Real.exp (-c₀*ε)) τ 1 θ
    let z := fun i => selectedContinuedRoot s (y i)
    ‖(coordinateProduct z)⁻¹+(coordinateProduct y)⁻¹‖ ≤
      2*(21+4*Real.exp (c₀+2*τ))^N := by
  dsimp only
  obtain ⟨hs0,hs1⟩ := selected_disk_parameter_envelope hN hε hε1 hc hs
  let E := Real.exp (c₀+2*τ)
  have hE : 0 < E := Real.exp_pos _
  have hy := selected_y_norm_envelope (by omega : 0<N) f hc₀ hτ hε hε1 hp0 hp1 hm0 hm1 θ
  have hz : ∀ i : Fin N,
      ‖(selectedContinuedRoot s (deformedPoint f (Real.exp (-c₀*ε)) τ 1 θ i))⁻¹‖ ≤ 21+4*E := by
    intro i
    have hW := selected_sourceW_envelope hs0 hs1 (hy i).1 (hy i).2
    have hh := quadratic_inverse_norm_envelope
      (continuedRoot_quadratic (sourceW s (deformedPoint f (Real.exp (-c₀*ε)) τ 1 θ i))) hW
    change ‖(selectedContinuedRoot s (deformedPoint f (Real.exp (-c₀*ε)) τ 1 θ i))⁻¹‖ ≤
      4*(5+E)+1 at hh
    linarith
  have hy' : ∀ i : Fin N,
      ‖(deformedPoint f (Real.exp (-c₀*ε)) τ 1 θ i)⁻¹‖ ≤ 21+4*E := by
    intro i
    have h := (hy i).2
    change ‖(deformedPoint f (Real.exp (-c₀*ε)) τ 1 θ i)⁻¹‖ ≤ E at h
    linarith
  simpa only [max_self] using inverse_global_numerator_norm_le
    (by positivity : 0 ≤ 21+4*E) (by positivity : 0 ≤ 21+4*E) hz hy'

end
end IsingBulk.Tail
