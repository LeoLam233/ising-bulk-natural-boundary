import IsingBulk.Joint.Transverse.FamilyParticleIdentity
import IsingBulk.Joint.RegularEdges.IndependentCoefficientJets

/-! # True ambient mixed-direction physical identities, without frozen family coordinates -/
namespace IsingBulk.Joint.Transverse
noncomputable section
open RegularEdges Set Filter Metric
open scoped Topology

def positivePhysicalParameter (b : ℝ) (K : Coupling) : NumeratorParameter :=
  (positiveParameter b K,(transferB K,positiveParticleScale K))
def negativeEvenPhysicalParameter (b : ℝ) (K : Coupling) : NumeratorParameter :=
  (negativeParameter b K,(-transferB K,negativeEvenParticleScale K))

theorem highFullParticle_independent (m : ℕ) {b : ℝ} {K : Coupling}
    (hK : K∈highDomain) (hS : S K≠0) (hB : 0<(transferB K).im)
    (hi : 0<(positiveParameter b K).im) :
    highFullParticle m K=positiveHighMultiplier K*
      independentAngularCoefficient (2*m) b (positivePhysicalParameter b K) :=
  highFullParticle_positive_model m (curve:=fun _=>K) (u:=positiveParameter b K) hK hS hB rfl hi

theorem lowFullParticle_positive_independent (m : ℕ) {b : ℝ} {K : Coupling}
    (hK : K∈lowDomain) (hS : S K≠0) (hB : 0<(transferB K).im)
    (hi : 0<(positiveParameter b K).im) :
    lowFullParticle m K=FormFactors.lowPrefactor K*
      independentAngularCoefficient (2*m+1) b (positivePhysicalParameter b K) :=
  lowFullParticle_positive_model m (curve:=fun _=>K) (u:=positiveParameter b K) hK hS hB rfl hi

theorem lowFullParticle_negative_independent (m : ℕ) {b : ℝ} {K : Coupling}
    (hK : K∈lowDomain) (hS : S K≠0) (hB : 0<(-transferB K).im)
    (hi : 0<(negativeParameter b K).im) :
    lowFullParticle m K=FormFactors.lowPrefactor K*
      independentAngularCoefficient (2*m+1) b (negativeEvenPhysicalParameter b K) :=
  lowFullParticle_negative_even_model m (curve:=fun _=>K) (u:=negativeParameter b K) hK hS hB rfl hi

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem positivePhysicalParameter_family_analyticAt (b : ℝ) {curve : E→Coupling} {x : E}
    (hc : AnalyticAt ℂ curve x) (hS : S (curve x)≠0) (hB : 0<(transferB (curve x)).im) :
    AnalyticAt ℂ (fun x=>positivePhysicalParameter b (curve x)) x := by
  have hC := (transferC_analyticAt hS).comp hc
  have hB' := transferB_family_analyticAt hc hS
  exact ((hC.sub hB').sub analyticAt_const).prod
    (hB'.prod (positiveParticleScale_family_analyticAt hc hS hB))

theorem negativeEvenPhysicalParameter_family_analyticAt (b : ℝ) {curve : E→Coupling} {x : E}
    (hc : AnalyticAt ℂ curve x) (hS : S (curve x)≠0) (hB : 0<(-transferB (curve x)).im) :
    AnalyticAt ℂ (fun x=>negativeEvenPhysicalParameter b (curve x)) x := by
  have hC := (transferC_analyticAt hS).comp hc
  have hB' := transferB_family_analyticAt hc hS
  exact ((hC.add hB').sub analyticAt_const).prod
    (hB'.neg.prod (negativeEvenParticleScale_family_analyticAt hc hS hB))

end
end IsingBulk.Joint.Transverse
