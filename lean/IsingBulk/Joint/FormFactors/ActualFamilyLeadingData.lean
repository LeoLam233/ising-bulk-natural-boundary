import IsingBulk.Joint.FormFactors.ActualFamilyTails
import IsingBulk.Joint.FormFactors.ComplexRatioPhysicalSide

/-! Actual complex-ratio inputs for the complete physical family asymptotics.
The parameter is complex lambda, the coupling is the constructed implicit
family, and the physical side is derived on a common polydisk. -/
namespace IsingBulk.Joint.FormFactors
noncomputable section
open Set Filter Metric
open scoped Topology

namespace ComplexRatioFamily
variable {b : ℝ} {amp : Coupling→ℂ} {z₀ lam₀ : ℂ}
variable (F : ComplexRatioFamily (Transverse.positiveParameter (b:ℂ)) amp 1 z₀ lam₀)

theorem positive_ratio_normalization_germ {lam : ℂ}
    (hl : lam∈closedBall lam₀ F.radius) :
    ∀ᶠu : ℂ in 𝓝 0,Transverse.positiveParameter b (F.coupling (u,lam))=u := by
  filter_upwards [ball_mem_nhds (0:ℂ) F.radius_pos] with u hu
  have hq : (u,lam)∈F.polydisk := ⟨ball_subset_closedBall hu,hl⟩
  exact F.edge_eq u lam (F.polydisk_bounds hq).1 (F.polydisk_bounds hq).2

theorem positive_ratio_center_analytic {lam : ℂ}
    (hl : lam∈closedBall lam₀ F.radius) : AnalyticAt ℂ F.coupling (0,lam) :=
  F.coupling_analytic 0 lam (F.polydisk_bounds (F.zero_mem_polydisk hl)).1
    (F.polydisk_bounds (F.zero_mem_polydisk hl)).2

theorem positive_ratio_center_scale_ne_zero {lam : ℂ}
    (hl : lam∈closedBall lam₀ F.radius) : S (F.coupling (0,lam))≠0 :=
  F.scale_ne_zero (F.zero_mem_polydisk hl)

theorem positive_ratio_center_anisotropy_pos {lam : ℂ}
    (hl : lam∈closedBall lam₀ F.radius) : 0<(transferB (F.coupling (0,lam))).im := by
  simpa only [one_mul,anisotropy] using F.anisotropy_sign (F.zero_mem_polydisk hl)

/-- The actual high-temperature family has all natural compact-family inputs
on a single closed complex-lambda disk. No same-side or frontier hypothesis is
supplied for nearby lambda values. -/
theorem actual_high_family_inputs
    (hK : (z₀,lam₀*z₀)∈closure highDomain) (hp : p (z₀,lam₀*z₀)^2≠1)
    (hS : S (z₀,lam₀*z₀)≠0) (hB : 0<(transferB (z₀,lam₀*z₀)).im) (hb : |b|<1) :
    ∃ρ : ℝ,0<ρ ∧ ρ≤F.radius ∧
      (∀lam∈closedBall lam₀ ρ,AnalyticAt ℂ F.coupling (0,lam)) ∧
      (∀lam∈closedBall lam₀ ρ,F.coupling (0,lam)∈frontier highDomain) ∧
      (∀lam∈closedBall lam₀ ρ,S (F.coupling (0,lam))≠0) ∧
      (∀lam∈closedBall lam₀ ρ,p (F.coupling (0,lam))^2≠1) ∧
      (∀lam∈closedBall lam₀ ρ,0<(transferB (F.coupling (0,lam))).im) ∧
      (∀lam∈closedBall lam₀ ρ,∀ᶠu : ℂ in 𝓝 0,Transverse.positiveParameter b (F.coupling (u,lam))=u) ∧
      ∀lam∈closedBall lam₀ ρ,∀u : ℂ,‖u‖≤ρ → (F.coupling (u,lam)∈highDomain ↔ 0<u.im) := by
  obtain ⟨ρ,hρ,hρF,hdata,hfrontier⟩ := positive_ratio_common_high_side F hK hp hS hB hb
  have hl' {lam : ℂ} (hl : lam∈closedBall lam₀ ρ) : ‖lam-lam₀‖≤ρ := by
    simpa only [mem_closedBall,dist_eq_norm] using hl
  have hc {lam : ℂ} (hl : lam∈closedBall lam₀ ρ) := hdata 0 lam (by simpa only [norm_zero] using hρ.le) (hl' hl)
  exact ⟨ρ,hρ,hρF,fun _ hl=>(hc hl).1,fun _ hl=>hfrontier _ (hl' hl),
    fun _ hl=>(hc hl).2.1,fun _ hl=>(hc hl).2.2.2.1,fun _ hl=>(hc hl).2.2.1,
    fun _ hl=>F.positive_ratio_normalization_germ (closedBall_subset_closedBall hρF hl),
    fun lam hl u hu=>(hdata u lam hu (hl' hl)).2.2.2.2⟩

/-- The identical complex-lambda construction on the actual low-temperature
component. It does not pass through a real-axis-only parameter family. -/
theorem actual_low_family_inputs
    (hK : (z₀,lam₀*z₀)∈closure lowDomain) (hp : p (z₀,lam₀*z₀)^2≠1)
    (hS : S (z₀,lam₀*z₀)≠0) (hB : 0<(transferB (z₀,lam₀*z₀)).im) (hb : |b|<1) :
    ∃ρ : ℝ,0<ρ ∧ ρ≤F.radius ∧
      (∀lam∈closedBall lam₀ ρ,AnalyticAt ℂ F.coupling (0,lam)) ∧
      (∀lam∈closedBall lam₀ ρ,F.coupling (0,lam)∈frontier lowDomain) ∧
      (∀lam∈closedBall lam₀ ρ,S (F.coupling (0,lam))≠0) ∧
      (∀lam∈closedBall lam₀ ρ,p (F.coupling (0,lam))^2≠1) ∧
      (∀lam∈closedBall lam₀ ρ,0<(transferB (F.coupling (0,lam))).im) ∧
      (∀lam∈closedBall lam₀ ρ,∀ᶠu : ℂ in 𝓝 0,Transverse.positiveParameter b (F.coupling (u,lam))=u) ∧
      ∀lam∈closedBall lam₀ ρ,∀u : ℂ,‖u‖≤ρ → (F.coupling (u,lam)∈lowDomain ↔ 0<u.im) := by
  obtain ⟨ρ,hρ,hρF,hdata,hfrontier⟩ := positive_ratio_common_low_side F hK hp hS hB hb
  have hl' {lam : ℂ} (hl : lam∈closedBall lam₀ ρ) : ‖lam-lam₀‖≤ρ := by
    simpa only [mem_closedBall,dist_eq_norm] using hl
  have hc {lam : ℂ} (hl : lam∈closedBall lam₀ ρ) := hdata 0 lam (by simpa only [norm_zero] using hρ.le) (hl' hl)
  exact ⟨ρ,hρ,hρF,fun _ hl=>(hc hl).1,fun _ hl=>hfrontier _ (hl' hl),
    fun _ hl=>(hc hl).2.1,fun _ hl=>(hc hl).2.2.2.1,fun _ hl=>(hc hl).2.2.1,
    fun _ hl=>F.positive_ratio_normalization_germ (closedBall_subset_closedBall hρF hl),
    fun lam hl u hu=>(hdata u lam hu (hl' hl)).2.2.2.2⟩

end ComplexRatioFamily
end
end IsingBulk.Joint.FormFactors
