import IsingBulk.Preferred22.SourceMixedFactors

/-! Primitive mixed calculus for every original factor of the literal
angular representative. These are the actual inverse occupancy matrix and
the two actual inverse-chart derivatives. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

theorem preferred_source_inverse_factors_mixed {N : ℕ}
    (τ δ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ)))
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2) :
    (∀ i b, PreferredMixedSmoothOn
      (fun z => (preferredContourMatrix τ p m z.2)⁻¹ i b) Ω) ∧
    (∀ i, PreferredMixedSmoothOn
      (fun z => preferredSourceUQ z.1 (preferredSourceCoordinate τ p m z.1 z.2 i)) Ω) ∧
    (∀ i, PreferredMixedSmoothOn
      (fun z => preferredSourceUDot z.1 (preferredSourceCoordinate τ p m z.1 z.2 i)) Ω) := by
  refine ⟨?_,?_,?_⟩
  · intro i b z hz
    have hM := preferredContourMatrix_inverse_contDiffAt τ p m hp hm z.2 (hpoint z hz).matrix
    have hR := (contDiffAt_pi.mp (contDiffAt_pi.mp hM i) b).comp z contDiffAt_snd
    exact ⟨hR,differentiableAt_const (𝕜:=ℂ) (x:=z.1) ((preferredContourMatrix τ p m z.2)⁻¹ i b)⟩
  · intro i z hz
    have h := hpoint z hz
    have hR := (preferredSourceInverseDerivatives_contDiffAt τ p m hp hm z.1 z.2
      h.trace_im h.upper h.inverse_analytic).1
    have hC := (preferredSourceInverseDerivatives_parameter_analyticAt τ p m z.1 z.2
      h.trace_im h.upper h.inverse_analytic).1
    exact ⟨contDiffAt_pi.mp hR i,(analyticAt_pi_iff.mp hC i).differentiableAt⟩
  · intro i z hz
    have h := hpoint z hz
    have hR := (preferredSourceInverseDerivatives_contDiffAt τ p m hp hm z.1 z.2
      h.trace_im h.upper h.inverse_analytic).2
    have hC := (preferredSourceInverseDerivatives_parameter_analyticAt τ p m z.1 z.2
      h.trace_im h.upper h.inverse_analytic).2
    exact ⟨contDiffAt_pi.mp hR i,(analyticAt_pi_iff.mp hC i).differentiableAt⟩

end
end IsingBulk.Preferred22
