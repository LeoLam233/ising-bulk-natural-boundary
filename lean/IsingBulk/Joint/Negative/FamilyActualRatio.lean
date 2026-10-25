import IsingBulk.Joint.FormFactors.ComplexRatioBounds
import IsingBulk.Joint.Negative.FamilyNormalizedModel
import IsingBulk.Joint.Negative.FamilyCanonicalNormalForm

/-! Actual complex-ratio admissibility for the complete negative-odd family
estimates. Both the anisotropy and its chosen particle root vary jointly. -/
namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic.NegativeNormalForm
open FormFactors
open scoped Topology

namespace NegativeRatioFamily
variable {edge amp : Coupling→ℂ} {z₀ lam₀ : ℂ}
variable (F : ComplexRatioFamily edge amp (-1) z₀ lam₀)

def rootAnisotropy (q : Coupling) : ℂ := Complex.sqrt (F.anisotropy q)
def particleAmplitude (q : Coupling) : ℂ := F.scale q*rootAnisotropy F q

theorem rootAnisotropy_sq (q : Coupling) : rootAnisotropy F q^2=F.anisotropy q :=
  sqrt_sq _

theorem anisotropy_slitPlane {q : Coupling} (hq : q∈F.polydisk) :
    F.anisotropy q∈Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  right
  have hh := F.anisotropy_sign hq
  intro hz
  simp only [hz,mul_zero,lt_self_iff_false] at hh

theorem rootAnisotropy_analyticOnNhd : AnalyticOnNhd ℂ (rootAnisotropy F) F.polydisk := by
  intro q hq
  exact (Complex.differentiableOn_sqrt.analyticOnNhd Complex.isOpen_slitPlane
    (F.anisotropy q) (anisotropy_slitPlane F hq)).comp (F.anisotropy_analyticOnNhd q hq)

theorem rootAnisotropy_ne_zero {q : Coupling} (hq : q∈F.polydisk) : rootAnisotropy F q≠0 := by
  intro hz
  have hh := rootAnisotropy_sq F q
  rw [hz,zero_pow (by decide : 2≠0)] at hh
  exact F.anisotropy_ne_zero hq hh.symm

theorem particleAmplitude_analyticOnNhd : AnalyticOnNhd ℂ (particleAmplitude F) F.polydisk :=
  fun q hq=>(F.scale_analyticOnNhd q hq).mul (rootAnisotropy_analyticOnNhd F q hq)

theorem particleAmplitude_ne_zero {q : Coupling} (hq : q∈F.polydisk) : particleAmplitude F q≠0 :=
  mul_ne_zero (F.scale_ne_zero hq) (rootAnisotropy_ne_zero F hq)

theorem particleAmplitude_sq {q : Coupling} (hq : q∈F.polydisk) :
    particleAmplitude F q^2=p (F.coupling q) := by
  rw [particleAmplitude,mul_pow,rootAnisotropy_sq]
  change S (F.coupling q)^2*(T (F.coupling q)/S (F.coupling q))=S (F.coupling q)*T (F.coupling q)
  have hS := F.scale_ne_zero hq
  change S (F.coupling q)≠0 at hS
  field_simp

theorem particleAmplitude_div_scale {q : Coupling} (hq : q∈F.polydisk) :
    particleAmplitude F q/S (F.coupling q)=rootAnisotropy F q := by
  exact mul_div_cancel_left₀ _ (F.scale_ne_zero hq)

theorem rootAnisotropy_central_analytic {lam : ℂ} (hl : lam∈closedBall lam₀ F.radius) :
    AnalyticAt ℂ (rootAnisotropy F) (0,lam) :=
  rootAnisotropy_analyticOnNhd F _ (F.zero_mem_polydisk hl)

theorem rootAnisotropy_central_ne_zero {lam : ℂ} (hl : lam∈closedBall lam₀ F.radius) :
    rootAnisotropy F (0,lam)≠0 := rootAnisotropy_ne_zero F (F.zero_mem_polydisk hl)

theorem particleAmplitude_all_mixed_jets (j : ℕ) :
    ∃M : ℝ,0<M ∧ ∀q∈F.polydisk,
      ‖iteratedFDeriv ℂ j (rootAnisotropy F) q‖≤M ∧
      ‖iteratedFDeriv ℂ j (particleAmplitude F) q‖≤M := by
  obtain ⟨M₁,hM₁,h₁⟩ := compact_analytic_all_jets_bound F.polydisk_isCompact
    (rootAnisotropy_analyticOnNhd F) j
  obtain ⟨M₂,hM₂,h₂⟩ := compact_analytic_all_jets_bound F.polydisk_isCompact
    (particleAmplitude_analyticOnNhd F) j
  exact ⟨M₁+M₂,add_pos hM₁ hM₂,fun q hq=>
    ⟨(h₁ q hq).trans (by linarith),(h₂ q hq).trans (by linarith)⟩⟩

end NegativeRatioFamily

theorem negative_ratio_actual_chart {b z₀ lam₀ : ℂ} {outerAmp : Coupling→ℂ}
    (F : ComplexRatioFamily (edgeParameter b) outerAmp (-1) z₀ lam₀)
    {q : Coupling} (hq : q∈F.polydisk) :
    S (F.coupling q)≠0 ∧ F.anisotropy q=T (F.coupling q)/S (F.coupling q) ∧
      transferC (F.coupling q)+transferB (F.coupling q)=b+F.anisotropy q*q.1 ∧
      NegativeRatioFamily.particleAmplitude F q^2=p (F.coupling q) ∧
      NegativeRatioFamily.particleAmplitude F q/S (F.coupling q)=NegativeRatioFamily.rootAnisotropy F q := by
  refine ⟨F.scale_ne_zero hq,rfl,?_,NegativeRatioFamily.particleAmplitude_sq F hq,
    NegativeRatioFamily.particleAmplitude_div_scale F hq⟩
  have he := F.edge_eq q.1 q.2 (F.polydisk_bounds hq).1 (F.polydisk_bounds hq).2
  have hB := F.anisotropy_ne_zero hq
  change transferB (F.coupling q)≠0 at hB
  unfold edgeParameter at he
  have hm := (div_eq_iff hB).mp he
  change transferC (F.coupling q)+transferB (F.coupling q)=b+transferB (F.coupling q)*q.1
  linear_combination hm

end
end IsingBulk.Joint.Negative
