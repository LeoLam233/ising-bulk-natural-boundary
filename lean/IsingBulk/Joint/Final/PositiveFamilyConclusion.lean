import IsingBulk.Joint.Transverse.FamilyQuantitativeEndpoint

namespace IsingBulk.Joint
noncomputable section
open Set Filter Metric Transverse Anisotropic
open scoped Topology

/-- Complete quantitative positive odd/even and negative-even clauses.
For each compact actual analytic family, a SINGLE common tube precedes all
ambient mixed derivative orders and all particle indices. The same package
retains the nonzero whole-bulk leading limit and every lower derivative.
Only geometric/analytic input data, never an estimate or physical-side map,
appear as hypotheses. -/
structure JointPositiveFamilyConclusion : Prop where
  high : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    {b : ℝ} (curve : ℂ × E→Coupling)
    {Q : Set E} (_hQ : IsCompact Q) (_hc : ∀eta∈Q,AnalyticAt ℂ curve (0,eta))
    (_hK : ∀eta∈Q,curve (0,eta)∈frontier highDomain)
    (_hS : ∀eta∈Q,S (curve (0,eta))≠0) (_hp : ∀eta∈Q,p (curve (0,eta))^2≠1)
    (_hB : ∀eta∈Q,0<(transferB (curve (0,eta))).im) (_hb : |b|<1)
    (_hprime : b∈primePhaseCosines)
    (_hn : ∀eta∈Q,∀ᶠu : ℂ in 𝓝 0,positiveParameter b (curve (u,eta))=u),
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
  low : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    {b : ℝ} (curve : ℂ × E→Coupling)
    {Q : Set E} (_hQ : IsCompact Q) (_hc : ∀eta∈Q,AnalyticAt ℂ curve (0,eta))
    (_hK : ∀eta∈Q,curve (0,eta)∈frontier lowDomain)
    (_hS : ∀eta∈Q,S (curve (0,eta))≠0) (_hp : ∀eta∈Q,p (curve (0,eta))^2≠1)
    (_hB : ∀eta∈Q,0<(transferB (curve (0,eta))).im) (_hb : |b|<1)
    (_hprime : b∈primePhaseCosines)
    (_hn : ∀eta∈Q,∀ᶠu : ℂ in 𝓝 0,positiveParameter b (curve (u,eta))=u),
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
  negative_even_low : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    {b : ℝ} (curve : ℂ × E→Coupling)
    {Q : Set E} (_hQ : IsCompact Q) (_hc : ∀eta∈Q,AnalyticAt ℂ curve (0,eta))
    (_hK : ∀eta∈Q,curve (0,eta)∈frontier lowDomain)
    (_hS : ∀eta∈Q,S (curve (0,eta))≠0) (_hp : ∀eta∈Q,p (curve (0,eta))^2≠1)
    (_hB : ∀eta∈Q,0<(-transferB (curve (0,eta))).im) (_hb : |b|<1)
    (_hprime : b∈primePhaseCosines)
    (_hn : ∀eta∈Q,∀ᶠu : ℂ in 𝓝 0,negativeParameter b (curve (u,eta))=u),
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

theorem joint_positive_family_conclusion : JointPositiveFamilyConclusion where
  high := @Transverse.positive_high_compact_family_quantitative
  low := @Transverse.positive_low_compact_family_quantitative
  negative_even_low := @Transverse.negative_even_low_compact_family_quantitative

end
end IsingBulk.Joint
