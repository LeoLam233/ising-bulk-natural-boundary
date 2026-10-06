import IsingBulk.Tail.SelectorTheorem
import IsingBulk.First.RadialDiskAdmissibility

/-! Source radial-disk specialization. Constants are selected before epsilon
and are shared by all particle numbers; the evaluation radius stays fixed
throughout each parameter-neighborhood identity. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First Filter
open scoped Topology

theorem radial_disk_source_margin {θ : ℝ} (hθ : 0 < Real.sin θ) :
    ∃ c₀ c₁ ε₀ : ℝ, 0 < c₀ ∧ c₀ < Real.sin θ/2 ∧ 0 < c₁ ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ s : ℂ,
        ‖s-IsingBulk.Branch.radialParameter θ ε‖ < c₁*ε →
        (Real.exp (-c₀*ε))⁻¹-Real.exp (-c₀*ε) < (sourceS s).im := by
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
  exact hmargin

 theorem radial_weighted_retraction {θ : ℝ} (hθ : 0 < Real.sin θ)
    (f : SelectorFunctions) (hf : RegularSelector f) {τ : ℝ} (hτ : 0 ≤ τ) :
    ∃ c₀ c₁ ε₀ : ℝ, 0 < c₀ ∧ c₀ < Real.sin θ/2 ∧ 0 < c₁ ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ s : ℂ,
        ‖s-IsingBulk.Branch.radialParameter θ ε‖ < c₁*ε → ∀ N : ℕ, 0 < N →
        upperFormFactor N s = selectedIntegral N f (Real.exp (-c₀*ε)) τ s+
          originalLowerIntegral N f (Real.exp (-c₀*ε)) τ s+
          currentIntegral N f (Real.exp (-c₀*ε)) τ s := by
  obtain ⟨c₀,c₁,ε₀,hc₀,hc₀small,hc₁,hε₀,hε₁,hm⟩ := radial_disk_source_margin hθ
  refine ⟨c₀,c₁,ε₀,hc₀,hc₀small,hc₁,hε₀,hε₁,?_⟩
  intro ε hε hεlt s hs N hN
  exact exact_weighted_retraction N hN f hf (Real.exp_pos _)
    (by rw [Real.exp_lt_one_iff]; nlinarith [mul_pos hc₀ hε]) hτ s (hm ε hε hεlt s hs)

 theorem selector_eventually_eq (N : ℕ) (hN : 0 < N) (f : SelectorFunctions) (hf : RegularSelector f)
    {r τ : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) {s : ℂ}
    (hmargin : r⁻¹-r < (sourceS s).im) :
    upperFormFactor N =ᶠ[𝓝 s] (fun t => selectedIntegral N f r τ t+
      originalLowerIntegral N f r τ t+currentIntegral N f r τ t) := by
  have hinv : 1 < r⁻¹ := (one_lt_inv₀ hr).mpr hr1
  have hs0 : s ≠ 0 := by
    intro he
    simp only [he,sourceS,inv_zero,add_zero,Complex.zero_im] at hmargin
    linarith
  have hc : ContinuousAt (fun t : ℂ => (sourceS t).im) s :=
    Complex.continuous_im.continuousAt.comp (continuousAt_id.add (continuousAt_id.inv₀ hs0))
  filter_upwards [hc.eventually (Ioi_mem_nhds hmargin)] with t ht
  exact exact_weighted_retraction N hN f hf hr hr1 hτ t ht

 theorem selector_iteratedDeriv_eq (N : ℕ) (hN : 0 < N) (f : SelectorFunctions) (hf : RegularSelector f)
    {r τ : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) {s : ℂ}
    (hmargin : r⁻¹-r < (sourceS s).im) (j : ℕ) :
    iteratedDeriv j (upperFormFactor N) s =
      iteratedDeriv j (fun t => selectedIntegral N f r τ t+
        originalLowerIntegral N f r τ t+currentIntegral N f r τ t) s :=
  (selector_eventually_eq N hN f hf hr hr1 hτ hmargin).iteratedDeriv_eq j

end
end IsingBulk.Tail
