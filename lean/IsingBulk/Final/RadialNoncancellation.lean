import IsingBulk.First.SelectedComplementBound

/-! Algebra and limit estimates for the final noncancellation step. These are
supporting lemmas, not a substitute for proving the source's infinite tail. -/
namespace IsingBulk.Final
noncomputable section
open Filter
open scoped Topology

/-- Converse to the FIRST square-root asymptotic conversion. -/
theorem sqrt_limit_of_isLittleO {F : ℝ → ℂ} {L : ℂ}
    (h : Asymptotics.IsLittleO (𝓝[>] (0 : ℝ))
      (fun e => F e - (Real.sqrt e : ℂ)⁻¹ * L)
      (fun e => (Real.sqrt e : ℂ)⁻¹)) :
    Tendsto (fun e : ℝ => Real.sqrt e • F e) (𝓝[>] 0) (𝓝 L) := by
  have hz := h.tendsto_div_nhds_zero
  have ht := hz.add_const L
  simp only [zero_add] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with e he
  have hn : (Real.sqrt e : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr he).ne'
  simp only [Complex.real_smul]
  field_simp
  ring

/-- A nonzero inverse-square-root leading coefficient rules out every bounded
radial segment. The conclusion is stronger than failure of one proposed bound. -/
theorem nonzero_sqrt_asymptotic_unbounded {F : ℝ → ℂ} {L : ℂ}
    (hL : L ≠ 0)
    (h : Asymptotics.IsLittleO (𝓝[>] (0 : ℝ))
      (fun e => F e - (Real.sqrt e : ℂ)⁻¹ * L)
      (fun e => (Real.sqrt e : ℂ)⁻¹)) :
    ∀ d : ℝ, 0 < d → ∀ C : ℝ, ∃ e : ℝ, 0 < e ∧ e < d ∧ C < ‖F e‖ := by
  intro d hd C
  by_contra hn
  push Not at hn
  have hb : Asymptotics.IsLittleO (𝓝[>] (0 : ℝ)) F
      (fun e => (Real.sqrt e : ℂ)⁻¹) := by
    apply IsingBulk.First.bounded_radial_term_isLittleO (show 0 < d/2 by positivity)
    intro e he hed
    exact hn e he (by linarith)
  have hz : Tendsto (fun e : ℝ => Real.sqrt e • F e) (𝓝[>] 0) (𝓝 (0 : ℂ)) := by
    apply sqrt_limit_of_isLittleO
    simpa only [mul_zero, sub_zero] using hb
  exact hL (tendsto_nhds_unique (sqrt_limit_of_isLittleO h) hz)

/-- Adding a genuinely bounded finite part and a proved smaller-order tail
preserves the leading coefficient. All hypotheses are exposed locally. -/
theorem asymptotic_add_bounded_add_tail {F B T : ℝ → ℂ} {L : ℂ} {d C : ℝ}
    (hd : 0 < d) (hB : ∀ e : ℝ, 0 < e → e ≤ d → ‖B e‖ ≤ C)
    (hF : Asymptotics.IsLittleO (𝓝[>] (0 : ℝ))
      (fun e => F e - (Real.sqrt e : ℂ)⁻¹ * L)
      (fun e => (Real.sqrt e : ℂ)⁻¹))
    (hT : Asymptotics.IsLittleO (𝓝[>] (0 : ℝ)) T
      (fun e => (Real.sqrt e : ℂ)⁻¹)) :
    Asymptotics.IsLittleO (𝓝[>] (0 : ℝ))
      (fun e => B e + F e + T e - (Real.sqrt e : ℂ)⁻¹ * L)
      (fun e => (Real.sqrt e : ℂ)⁻¹) := by
  have h := ((IsingBulk.First.bounded_radial_term_isLittleO hd hB).add hF).add hT
  convert h using 1
  ext e
  ring

end
end IsingBulk.Final
