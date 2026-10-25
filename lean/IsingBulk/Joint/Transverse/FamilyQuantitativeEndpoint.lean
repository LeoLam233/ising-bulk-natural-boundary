import IsingBulk.Joint.Transverse.FamilyPhysicalMixedTails
import IsingBulk.Joint.Transverse.FamilyNegativeEvenLeading

/-! # Quantitative common-family endpoints for the literal physical bulk

The finite lower orders, first resonant order, finite higher orders, and infinite
particle tail have all been included in the full-bulk limit. The extra tail clause
controls every ambient mixed Fréchet derivative on one common scalar tube.
-/
namespace IsingBulk.Joint.Transverse
noncomputable section
open IsingBulk.Anisotropic Set Filter Metric
open scoped Topology
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Actual full-bulk uniform noncancellation and complete mixed tails for an
arbitrary compact normalized analytic family, with the physical side derived. -/
theorem positive_high_compact_family_quantitative {b : ℝ} (curve : ℂ × E→Coupling)
    {Q : Set E} (hQ : IsCompact Q) (hc : ∀eta∈Q,AnalyticAt ℂ curve (0,eta))
    (hK : ∀eta∈Q,curve (0,eta)∈frontier highDomain)
    (hS : ∀eta∈Q,S (curve (0,eta))≠0) (hp : ∀eta∈Q,p (curve (0,eta))^2≠1)
    (hB : ∀eta∈Q,0<(transferB (curve (0,eta))).im) (hb : |b|<1)
    (hprime : b∈primePhaseCosines)
    (hn : ∀eta∈Q,∀ᶠu : ℂ in 𝓝 0,positiveParameter b (curve (u,eta))=u) :
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
        (fun u=>FormFactors.highNormalizedBulk (curve (u,eta))) (Complex.I*(t:ℂ)^2)‖) := by
  obtain ⟨q,k,c,hq,hcritical,hcpos,hL,hlimits,hunbounded⟩ := positive_high_compact_family_leading curve hQ hc hK hS hp hB hb hprime hn
  obtain ⟨r,hr,htube⟩ := compact_family_positive_high_tube curve hQ hc hK hS hp hB hb hn
  obtain ⟨d,hd,hjets⟩ := positive_high_compact_family_particle_mixed_tails curve hQ hc hK hS hp hB hb hn
  refine ⟨q,k,min r d,c,hq,hcritical,lt_min hr hd,hcpos,hL,?_,?_,hlimits,hunbounded⟩
  · intro eta heta u hu
    exact htube eta heta u (hu.trans_le (min_le_left _ _))
  · intro j
    obtain ⟨G,hG,hG0,hbound⟩ := hjets j
    exact ⟨G,hG,hG0,fun eta heta u hu hi l=>hbound eta heta u (hu.trans_le (min_le_right _ _)) hi l⟩

/-- Actual full-bulk uniform noncancellation and complete mixed tails for an
arbitrary compact normalized analytic family, with the physical side derived. -/
theorem positive_low_compact_family_quantitative {b : ℝ} (curve : ℂ × E→Coupling)
    {Q : Set E} (hQ : IsCompact Q) (hc : ∀eta∈Q,AnalyticAt ℂ curve (0,eta))
    (hK : ∀eta∈Q,curve (0,eta)∈frontier lowDomain)
    (hS : ∀eta∈Q,S (curve (0,eta))≠0) (hp : ∀eta∈Q,p (curve (0,eta))^2≠1)
    (hB : ∀eta∈Q,0<(transferB (curve (0,eta))).im) (hb : |b|<1)
    (hprime : b∈primePhaseCosines)
    (hn : ∀eta∈Q,∀ᶠu : ℂ in 𝓝 0,positiveParameter b (curve (u,eta))=u) :
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
        (fun u=>FormFactors.lowNormalizedBulk (curve (u,eta))) (Complex.I*(t:ℂ)^2)‖) := by
  obtain ⟨q,k,c,hcritical,hcpos,hL,hlimits,hunbounded⟩ := positive_low_compact_family_leading curve hQ hc hK hS hp hB hb hprime hn
  obtain ⟨r,hr,htube⟩ := compact_family_positive_low_tube curve hQ hc hK hS hp hB hb hn
  obtain ⟨d,hd,hjets⟩ := positive_low_compact_family_particle_mixed_tails curve hQ hc hK hS hp hB hb hn
  refine ⟨q,k,min r d,c,hcritical,lt_min hr hd,hcpos,hL,?_,?_,hlimits,hunbounded⟩
  · intro eta heta u hu
    exact htube eta heta u (hu.trans_le (min_le_left _ _))
  · intro j
    obtain ⟨G,hG,hG0,hbound⟩ := hjets j
    exact ⟨G,hG,hG0,fun eta heta u hu hi l=>hbound eta heta u (hu.trans_le (min_le_right _ _)) hi l⟩

/-- Actual full-bulk uniform noncancellation and complete mixed tails for an
arbitrary compact normalized analytic family, with the physical side derived. -/
theorem negative_even_low_compact_family_quantitative {b : ℝ} (curve : ℂ × E→Coupling)
    {Q : Set E} (hQ : IsCompact Q) (hc : ∀eta∈Q,AnalyticAt ℂ curve (0,eta))
    (hK : ∀eta∈Q,curve (0,eta)∈frontier lowDomain)
    (hS : ∀eta∈Q,S (curve (0,eta))≠0) (hp : ∀eta∈Q,p (curve (0,eta))^2≠1)
    (hB : ∀eta∈Q,0<(-transferB (curve (0,eta))).im) (hb : |b|<1)
    (hprime : b∈primePhaseCosines)
    (hn : ∀eta∈Q,∀ᶠu : ℂ in 𝓝 0,negativeParameter b (curve (u,eta))=u) :
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
        (fun u=>FormFactors.lowNormalizedBulk (curve (u,eta))) (Complex.I*(t:ℂ)^2)‖) := by
  obtain ⟨q,k,c,hcritical,hcpos,hL,hlimits,hunbounded⟩ := negative_even_low_compact_family_leading curve hQ hc hK hS hp hB hb hprime hn
  obtain ⟨r,hr,htube⟩ := compact_family_negative_low_tube curve hQ hc hK hS hp hB hb hn
  obtain ⟨d,hd,hjets⟩ := negative_even_low_compact_family_particle_mixed_tails curve hQ hc hK hS hp hB hb hn
  refine ⟨q,k,min r d,c,hcritical,lt_min hr hd,hcpos,hL,?_,?_,hlimits,hunbounded⟩
  · intro eta heta u hu
    exact htube eta heta u (hu.trans_le (min_le_left _ _))
  · intro j
    obtain ⟨G,hG,hG0,hbound⟩ := hjets j
    exact ⟨G,hG,hG0,fun eta heta u hu hi l=>hbound eta heta u (hu.trans_le (min_le_right _ _)) hi l⟩

end
end IsingBulk.Joint.Transverse
