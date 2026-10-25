import IsingBulk.Joint.FormFactors.ActualFamilyLeadingNegativeFamily
import IsingBulk.Joint.FormFactors.ComplexRatioNegativeSide

/-! All natural compact-family hypotheses for the actual additive negative
low-temperature complex-ratio family, with the true physical side derived. -/
namespace IsingBulk.Joint.FormFactors
noncomputable section
open Set Filter Metric
open scoped Topology
namespace ComplexRatioFamily
variable {b : ℝ} {amp : Coupling→ℂ} {z₀ lam₀ : ℂ}
variable (F : ComplexRatioFamily (Transverse.negativeParameter (b:ℂ)) amp (-1) z₀ lam₀)

/-- The identical complex-lambda construction on the actual low-temperature
component. It does not pass through a real-axis-only parameter family. -/
theorem actual_negative_even_low_family_inputs
    (hK : (z₀,lam₀*z₀)∈closure lowDomain) (hp : p (z₀,lam₀*z₀)^2≠1)
    (hS : S (z₀,lam₀*z₀)≠0) (hB : (transferB (z₀,lam₀*z₀)).im<0) (hb : |b|<1) :
    ∃ρ : ℝ,0<ρ ∧ ρ≤F.radius ∧
      (∀lam∈closedBall lam₀ ρ,AnalyticAt ℂ F.coupling (0,lam)) ∧
      (∀lam∈closedBall lam₀ ρ,F.coupling (0,lam)∈frontier lowDomain) ∧
      (∀lam∈closedBall lam₀ ρ,S (F.coupling (0,lam))≠0) ∧
      (∀lam∈closedBall lam₀ ρ,p (F.coupling (0,lam))^2≠1) ∧
      (∀lam∈closedBall lam₀ ρ,(transferB (F.coupling (0,lam))).im<0) ∧
      (∀lam∈closedBall lam₀ ρ,∀ᶠu : ℂ in 𝓝 0,Transverse.negativeParameter b (F.coupling (u,lam))=u) ∧
      ∀lam∈closedBall lam₀ ρ,∀u : ℂ,‖u‖≤ρ → (F.coupling (u,lam)∈lowDomain ↔ 0<u.im) := by
  obtain ⟨ρ,hρ,hρF,hdata,hfrontier⟩ := negative_ratio_raw_common_low_side F hK hp hS hB hb
  have hl' {lam : ℂ} (hl : lam∈closedBall lam₀ ρ) : ‖lam-lam₀‖≤ρ := by
    simpa only [mem_closedBall,dist_eq_norm] using hl
  have hc {lam : ℂ} (hl : lam∈closedBall lam₀ ρ) := hdata 0 lam (by simpa only [norm_zero] using hρ.le) (hl' hl)
  exact ⟨ρ,hρ,hρF,fun _ hl=>(hc hl).1,fun _ hl=>hfrontier _ (hl' hl),
    fun _ hl=>(hc hl).2.1,fun _ hl=>(hc hl).2.2.2.1,fun _ hl=>(hc hl).2.2.1,
    fun _ hl=>F.negative_additive_ratio_normalization_germ (closedBall_subset_closedBall hρF hl),
    fun lam hl u hu=>(hdata u lam hu (hl' hl)).2.2.2.2⟩


end ComplexRatioFamily
end
end IsingBulk.Joint.FormFactors
