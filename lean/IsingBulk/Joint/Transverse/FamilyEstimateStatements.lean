import IsingBulk.Joint.Transverse.FamilyQuantitativeEndpoint
import IsingBulk.Joint.Negative.FamilyMixedConclusion
import IsingBulk.Joint.Negative.FamilyPhysicalConclusion

/-! Named result propositions for the actual complete family estimates.
These are conclusions of the proved physical estimates, never hypotheses
standing in for any singularity or majorant argument. -/
namespace IsingBulk.Joint.Transverse
noncomputable section
open IsingBulk.Anisotropic Set Filter Metric
open scoped Topology
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def PositiveHighFamilyEstimates (b : ℝ) (curve : ℂ × E→Coupling) (Q : Set E) : Prop :=
    ∃q k : ℕ,∃δ c : ℝ,1≤q ∧ 2*k+1=(2*q+1)^2 ∧ 0<δ ∧ 0<c ∧
      (∀eta∈Q,c≤‖positiveHighLeading (2*q) k b curve eta‖) ∧
      (∀eta∈Q,∀u : ℂ,‖u‖<δ →
        AnalyticAt ℂ curve (u,eta) ∧ S (curve (u,eta))≠0 ∧
        0<(transferB (curve (u,eta))).im ∧
        positiveParameter b (curve (u,eta))=u ∧ (curve (u,eta)∈highDomain ↔ 0<u.im)) ∧
      (∀j : ℕ,∃G : ℕ→ℝ,Summable G ∧ (∀l,0≤G l) ∧
        ∀eta∈Q,∀u : ℂ,‖u‖<δ → 0<u.im → ∀l : ℕ,
        ‖iteratedFDeriv ℂ j (fun x=>highFullParticle (j+2+l) (curve x)) (u,eta)‖≤G l) ∧
      (∀j≤k,TendstoUniformlyOn (fun (t : ℝ) eta=>(t^2) • iteratedDeriv j
        (fun u=>FormFactors.highNormalizedBulk (curve (u,eta))) (Complex.I*(t:ℂ)^2))
        (fun eta=>if j=k then positiveHighLeading (2*q) k b curve eta else 0) (𝓝[>] (0:ℝ)) Q) ∧
      (∀M : ℝ,∀ᶠt : ℝ in 𝓝[>] 0,∀eta∈Q,M<‖iteratedDeriv k
        (fun u=>FormFactors.highNormalizedBulk (curve (u,eta))) (Complex.I*(t:ℂ)^2)‖)

def PositiveLowFamilyEstimates (b : ℝ) (curve : ℂ × E→Coupling) (Q : Set E) : Prop :=
    ∃q k : ℕ,∃δ c : ℝ,2*(k+1)=(2*q+2)^2 ∧ 0<δ ∧ 0<c ∧
      (∀eta∈Q,c≤‖positiveLowLeading (2*q+1) k b curve eta‖) ∧
      (∀eta∈Q,∀u : ℂ,‖u‖<δ →
        AnalyticAt ℂ curve (u,eta) ∧ S (curve (u,eta))≠0 ∧
        0<(transferB (curve (u,eta))).im ∧
        positiveParameter b (curve (u,eta))=u ∧ (curve (u,eta)∈lowDomain ↔ 0<u.im)) ∧
      (∀j : ℕ,∃G : ℕ→ℝ,Summable G ∧ (∀l,0≤G l) ∧
        ∀eta∈Q,∀u : ℂ,‖u‖<δ → 0<u.im → ∀l : ℕ,
        ‖iteratedFDeriv ℂ j (fun x=>lowFullParticle (j+2+l) (curve x)) (u,eta)‖≤G l) ∧
      (∀j≤k,TendstoUniformlyOn (fun (t : ℝ) eta=>t • iteratedDeriv j
        (fun u=>FormFactors.lowNormalizedBulk (curve (u,eta))) (Complex.I*(t:ℂ)^2))
        (fun eta=>if j=k then positiveLowLeading (2*q+1) k b curve eta else 0) (𝓝[>] (0:ℝ)) Q) ∧
      (∀M : ℝ,∀ᶠt : ℝ in 𝓝[>] 0,∀eta∈Q,M<‖iteratedDeriv k
        (fun u=>FormFactors.lowNormalizedBulk (curve (u,eta))) (Complex.I*(t:ℂ)^2)‖)

def NegativeEvenLowFamilyEstimates (b : ℝ) (curve : ℂ × E→Coupling) (Q : Set E) : Prop :=
    ∃q k : ℕ,∃δ c : ℝ,2*(k+1)=(2*q+2)^2 ∧ 0<δ ∧ 0<c ∧
      (∀eta∈Q,c≤‖negativeEvenLowLeading (2*q+1) k b curve eta‖) ∧
      (∀eta∈Q,∀u : ℂ,‖u‖<δ →
        AnalyticAt ℂ curve (u,eta) ∧ S (curve (u,eta))≠0 ∧
        0<(-transferB (curve (u,eta))).im ∧
        negativeParameter b (curve (u,eta))=u ∧ (curve (u,eta)∈lowDomain ↔ 0<u.im)) ∧
      (∀j : ℕ,∃G : ℕ→ℝ,Summable G ∧ (∀l,0≤G l) ∧
        ∀eta∈Q,∀u : ℂ,‖u‖<δ → 0<u.im → ∀l : ℕ,
        ‖iteratedFDeriv ℂ j (fun x=>lowFullParticle (j+2+l) (curve x)) (u,eta)‖≤G l) ∧
      (∀j≤k,TendstoUniformlyOn (fun (t : ℝ) eta=>t • iteratedDeriv j
        (fun u=>FormFactors.lowNormalizedBulk (curve (u,eta))) (Complex.I*(t:ℂ)^2))
        (fun eta=>if j=k then negativeEvenLowLeading (2*q+1) k b curve eta else 0) (𝓝[>] (0:ℝ)) Q) ∧
      (∀M : ℝ,∀ᶠt : ℝ in 𝓝[>] 0,∀eta∈Q,M<‖iteratedDeriv k
        (fun u=>FormFactors.lowNormalizedBulk (curve (u,eta))) (Complex.I*(t:ℂ)^2)‖)

def NegativeHighFamilyMixedEstimates (curve : ℂ × E→Coupling) (Q : Set E) : Prop :=
    ∃δ : ℝ,0<δ ∧
      (∀eta∈Q,∀u : ℂ,‖u‖<δ →
        (curve (u,eta)∈highDomain ↔ 0<(transferB (curve (u,eta))*u).im)) ∧
      ∀j : ℕ,∃G : ℕ→ℝ,Summable G ∧ (∀k,0≤G k) ∧
      ∀eta∈Q,∀u : ℂ,‖u‖<δ → 0<(transferB (curve (u,eta))*u).im → ∀k : ℕ,
      ‖iteratedFDeriv ℂ j (fun q=>highFullParticle (j+2+k) (curve q)) (u,eta)‖≤G k

/-- Both the true negative-odd boundary obstruction and its literal full
physical all-mixed tail estimates, using a canonical analytic particle root. -/
def NegativeHighFamilyEstimates (curve : ℂ × E→Coupling) (Q : Set E) : Prop :=
  Negative.CompactNegativePhysicalObstruction curve
    (fun q=>negativeEvenParticleRoot (curve q)) Q ∧
  NegativeHighFamilyMixedEstimates curve Q

theorem positive_high_normalized_family_estimates {b : ℝ} (curve : ℂ × E→Coupling)
    {Q : Set E} (hQ : IsCompact Q) (hc : ∀eta∈Q,AnalyticAt ℂ curve (0,eta))
    (hK : ∀eta∈Q,curve (0,eta)∈frontier highDomain)
    (hS : ∀eta∈Q,S (curve (0,eta))≠0) (hp : ∀eta∈Q,p (curve (0,eta))^2≠1)
    (hB : ∀eta∈Q,0<(transferB (curve (0,eta))).im) (hb : |b|<1)
    (hprime : b∈primePhaseCosines)
    (hn : ∀eta∈Q,∀ᶠu : ℂ in 𝓝 0,positiveParameter b (curve (u,eta))=u) :
    PositiveHighFamilyEstimates b curve Q :=
  positive_high_compact_family_quantitative curve hQ hc hK hS hp hB hb hprime hn

theorem positive_low_normalized_family_estimates {b : ℝ} (curve : ℂ × E→Coupling)
    {Q : Set E} (hQ : IsCompact Q) (hc : ∀eta∈Q,AnalyticAt ℂ curve (0,eta))
    (hK : ∀eta∈Q,curve (0,eta)∈frontier lowDomain)
    (hS : ∀eta∈Q,S (curve (0,eta))≠0) (hp : ∀eta∈Q,p (curve (0,eta))^2≠1)
    (hB : ∀eta∈Q,0<(transferB (curve (0,eta))).im) (hb : |b|<1)
    (hprime : b∈primePhaseCosines)
    (hn : ∀eta∈Q,∀ᶠu : ℂ in 𝓝 0,positiveParameter b (curve (u,eta))=u) :
    PositiveLowFamilyEstimates b curve Q :=
  positive_low_compact_family_quantitative curve hQ hc hK hS hp hB hb hprime hn

theorem negative_even_low_normalized_family_estimates {b : ℝ} (curve : ℂ × E→Coupling)
    {Q : Set E} (hQ : IsCompact Q) (hc : ∀eta∈Q,AnalyticAt ℂ curve (0,eta))
    (hK : ∀eta∈Q,curve (0,eta)∈frontier lowDomain)
    (hS : ∀eta∈Q,S (curve (0,eta))≠0) (hp : ∀eta∈Q,p (curve (0,eta))^2≠1)
    (hB : ∀eta∈Q,0<(-transferB (curve (0,eta))).im) (hb : |b|<1)
    (hprime : b∈primePhaseCosines)
    (hn : ∀eta∈Q,∀ᶠu : ℂ in 𝓝 0,negativeParameter b (curve (u,eta))=u) :
    NegativeEvenLowFamilyEstimates b curve Q :=
  negative_even_low_compact_family_quantitative curve hQ hc hK hS hp hB hb hprime hn

end
end IsingBulk.Joint.Transverse
