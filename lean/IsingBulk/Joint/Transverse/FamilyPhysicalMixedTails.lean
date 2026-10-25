import IsingBulk.Joint.Transverse.FamilyIndependentIdentity
import IsingBulk.Joint.Transverse.FamilyPhysicalLeading
import IsingBulk.Joint.FormFactors.GenericCompactMixedTails

/-! # Complete physical tails in every ambient mixed family direction

The model substitution uses the actual edge coordinate on the ambient parameter
space. Fiber normalization is never differentiated in parameter directions.
-/
namespace IsingBulk.Joint.Transverse
noncomputable section
open RegularEdges Set Filter Metric
open scoped Topology
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- One radius before all derivative orders controls all true mixed Fréchet jets
of every sufficiently high particle of the literal physical series. -/
theorem positive_high_compact_family_particle_mixed_tails {b : ℝ} (curve : ℂ × E→Coupling)
    {Q : Set E} (hQ : IsCompact Q) (hc : ∀eta∈Q,AnalyticAt ℂ curve (0,eta))
    (hK : ∀eta∈Q,curve (0,eta)∈frontier highDomain)
    (hS : ∀eta∈Q,S (curve (0,eta))≠0) (hp : ∀eta∈Q,p (curve (0,eta))^2≠1)
    (hB : ∀eta∈Q,0<(transferB (curve (0,eta))).im) (hb : |b|<1)
    (hn : ∀eta∈Q,∀ᶠu : ℂ in 𝓝 0,positiveParameter b (curve (u,eta))=u) :
    ∃δ : ℝ,0<δ ∧ ∀j : ℕ,∃G : ℕ→ℝ,Summable G ∧ (∀k,0≤G k) ∧
      ∀eta∈Q,∀u : ℂ,‖u‖<δ → 0<u.im → ∀k : ℕ,
      ‖iteratedFDeriv ℂ j (fun q=>highFullParticle (j+2+k) (curve q)) (u,eta)‖≤G k := by
  obtain ⟨r,hr,htube⟩ := compact_family_positive_high_tube curve hQ hc hK hS hp hB hb hn
  obtain ⟨d,hd,hjets⟩ := FormFactors.compact_joint_parametric_coefficient_mixed_tails
    (fun q=>positivePhysicalParameter b (curve q)) (fun q=>positiveHighMultiplier (curve q)) hb hQ
    (fun eta heta=>positivePhysicalParameter_family_analyticAt b (hc eta heta) (hS eta heta) (hB eta heta))
    (fun eta heta=>positiveHighMultiplier_family_analyticAt (hc eta heta) (hK eta heta).1 (hp eta heta) (hS eta heta) (hB eta heta))
    (fun eta heta=>Filter.EventuallyEq.eq_of_nhds (hn eta heta)) hB
    (fun eta heta=>div_ne_zero (hS eta heta) (positiveParticleRoot_ne_zero (hS eta heta) (hB eta heta)))
  refine ⟨min r d,lt_min hr hd,?_⟩
  intro j
  obtain ⟨G,hG,hG0,hbound⟩ := hjets j
  refine ⟨fun k=>G (1+2*k+0),hG.comp_injective (by intro x y h; dsimp at h; omega),
    fun k=>hG0 _,?_⟩
  intro eta heta u hu hi k
  have ht := htube eta heta u (hu.trans_le (min_le_left _ _))
  have hpa := positivePhysicalParameter_family_analyticAt b ht.1 ht.2.1 ht.2.2.1
  have hsi : ContinuousAt (fun q=>S (curve q)) (u,eta) :=
    Complex.continuous_sinh.continuousAt.comp ht.1.continuousAt.fst
  have heq : (fun q=>highFullParticle (j+2+k) (curve q)) =ᶠ[𝓝 (u,eta)]
      (fun q=>positiveHighMultiplier (curve q)*independentAngularCoefficient (2*(j+2+k)+0) b (positivePhysicalParameter b (curve q))) := by
    filter_upwards [ht.1.continuousAt.preimage_mem_nhds (highDomain_isOpen.mem_nhds (ht.2.2.2.2.mpr hi)),
      hsi.eventually_ne ht.2.1,
      continuousAt_const.eventually_lt (Complex.continuous_im.continuousAt.comp hpa.continuousAt.snd.fst) ht.2.2.1,
      continuousAt_const.eventually_lt (Complex.continuous_im.continuousAt.comp hpa.continuousAt.fst)
        (show 0<(positiveParameter b (curve (u,eta))).im by rw [ht.2.2.2.1]; exact hi)] with q hq hs hb' hi'
    exact highFullParticle_independent _ hq hs hb' hi'
  rw [(heq.iteratedFDeriv ℂ j).eq_of_nhds]
  have hh := hbound eta heta u (hu.trans_le (min_le_right _ _))
    (show 0<(positivePhysicalParameter b (curve (u,eta))).1.im by change 0<(positiveParameter b (curve (u,eta))).im; rw [ht.2.2.2.1]; exact hi) (1+2*k+0)
  simpa only [show 2*j+3+(1+2*k+0)=2*(j+2+k)+0 by omega] using hh

/-- One radius before all derivative orders controls all true mixed Fréchet jets
of every sufficiently high particle of the literal physical series. -/
theorem positive_low_compact_family_particle_mixed_tails {b : ℝ} (curve : ℂ × E→Coupling)
    {Q : Set E} (hQ : IsCompact Q) (hc : ∀eta∈Q,AnalyticAt ℂ curve (0,eta))
    (hK : ∀eta∈Q,curve (0,eta)∈frontier lowDomain)
    (hS : ∀eta∈Q,S (curve (0,eta))≠0) (hp : ∀eta∈Q,p (curve (0,eta))^2≠1)
    (hB : ∀eta∈Q,0<(transferB (curve (0,eta))).im) (hb : |b|<1)
    (hn : ∀eta∈Q,∀ᶠu : ℂ in 𝓝 0,positiveParameter b (curve (u,eta))=u) :
    ∃δ : ℝ,0<δ ∧ ∀j : ℕ,∃G : ℕ→ℝ,Summable G ∧ (∀k,0≤G k) ∧
      ∀eta∈Q,∀u : ℂ,‖u‖<δ → 0<u.im → ∀k : ℕ,
      ‖iteratedFDeriv ℂ j (fun q=>lowFullParticle (j+2+k) (curve q)) (u,eta)‖≤G k := by
  obtain ⟨r,hr,htube⟩ := compact_family_positive_low_tube curve hQ hc hK hS hp hB hb hn
  obtain ⟨d,hd,hjets⟩ := FormFactors.compact_joint_parametric_coefficient_mixed_tails
    (fun q=>positivePhysicalParameter b (curve q)) (fun q=>FormFactors.lowPrefactor (curve q)) hb hQ
    (fun eta heta=>positivePhysicalParameter_family_analyticAt b (hc eta heta) (hS eta heta) (hB eta heta))
    (fun eta heta=>(lowPrefactor_boundary_analyticAt (hK eta heta).1 (hp eta heta)).comp (hc eta heta))
    (fun eta heta=>Filter.EventuallyEq.eq_of_nhds (hn eta heta)) hB
    (fun eta heta=>div_ne_zero (hS eta heta) (positiveParticleRoot_ne_zero (hS eta heta) (hB eta heta)))
  refine ⟨min r d,lt_min hr hd,?_⟩
  intro j
  obtain ⟨G,hG,hG0,hbound⟩ := hjets j
  refine ⟨fun k=>G (1+2*k+1),hG.comp_injective (by intro x y h; dsimp at h; omega),
    fun k=>hG0 _,?_⟩
  intro eta heta u hu hi k
  have ht := htube eta heta u (hu.trans_le (min_le_left _ _))
  have hpa := positivePhysicalParameter_family_analyticAt b ht.1 ht.2.1 ht.2.2.1
  have hsi : ContinuousAt (fun q=>S (curve q)) (u,eta) :=
    Complex.continuous_sinh.continuousAt.comp ht.1.continuousAt.fst
  have heq : (fun q=>lowFullParticle (j+2+k) (curve q)) =ᶠ[𝓝 (u,eta)]
      (fun q=>FormFactors.lowPrefactor (curve q)*independentAngularCoefficient (2*(j+2+k)+1) b (positivePhysicalParameter b (curve q))) := by
    filter_upwards [ht.1.continuousAt.preimage_mem_nhds (lowDomain_isOpen.mem_nhds (ht.2.2.2.2.mpr hi)),
      hsi.eventually_ne ht.2.1,
      continuousAt_const.eventually_lt (Complex.continuous_im.continuousAt.comp hpa.continuousAt.snd.fst) ht.2.2.1,
      continuousAt_const.eventually_lt (Complex.continuous_im.continuousAt.comp hpa.continuousAt.fst)
        (show 0<(positiveParameter b (curve (u,eta))).im by rw [ht.2.2.2.1]; exact hi)] with q hq hs hb' hi'
    exact lowFullParticle_positive_independent _ hq hs hb' hi'
  rw [(heq.iteratedFDeriv ℂ j).eq_of_nhds]
  have hh := hbound eta heta u (hu.trans_le (min_le_right _ _))
    (show 0<(positivePhysicalParameter b (curve (u,eta))).1.im by change 0<(positiveParameter b (curve (u,eta))).im; rw [ht.2.2.2.1]; exact hi) (1+2*k+1)
  simpa only [show 2*j+3+(1+2*k+1)=2*(j+2+k)+1 by omega] using hh

/-- One radius before all derivative orders controls all true mixed Fréchet jets
of every sufficiently high particle of the literal physical series. -/
theorem negative_even_low_compact_family_particle_mixed_tails {b : ℝ} (curve : ℂ × E→Coupling)
    {Q : Set E} (hQ : IsCompact Q) (hc : ∀eta∈Q,AnalyticAt ℂ curve (0,eta))
    (hK : ∀eta∈Q,curve (0,eta)∈frontier lowDomain)
    (hS : ∀eta∈Q,S (curve (0,eta))≠0) (hp : ∀eta∈Q,p (curve (0,eta))^2≠1)
    (hB : ∀eta∈Q,0<(-transferB (curve (0,eta))).im) (hb : |b|<1)
    (hn : ∀eta∈Q,∀ᶠu : ℂ in 𝓝 0,negativeParameter b (curve (u,eta))=u) :
    ∃δ : ℝ,0<δ ∧ ∀j : ℕ,∃G : ℕ→ℝ,Summable G ∧ (∀k,0≤G k) ∧
      ∀eta∈Q,∀u : ℂ,‖u‖<δ → 0<u.im → ∀k : ℕ,
      ‖iteratedFDeriv ℂ j (fun q=>lowFullParticle (j+2+k) (curve q)) (u,eta)‖≤G k := by
  obtain ⟨r,hr,htube⟩ := compact_family_negative_low_tube curve hQ hc hK hS hp hB hb hn
  obtain ⟨d,hd,hjets⟩ := FormFactors.compact_joint_parametric_coefficient_mixed_tails
    (fun q=>negativeEvenPhysicalParameter b (curve q)) (fun q=>FormFactors.lowPrefactor (curve q)) hb hQ
    (fun eta heta=>negativeEvenPhysicalParameter_family_analyticAt b (hc eta heta) (hS eta heta) (hB eta heta))
    (fun eta heta=>(lowPrefactor_boundary_analyticAt (hK eta heta).1 (hp eta heta)).comp (hc eta heta))
    (fun eta heta=>Filter.EventuallyEq.eq_of_nhds (hn eta heta)) hB
    (fun eta heta=>div_ne_zero (mul_ne_zero Complex.I_ne_zero (hS eta heta)) (negativeEvenParticleRoot_ne_zero (hS eta heta) (hB eta heta)))
  refine ⟨min r d,lt_min hr hd,?_⟩
  intro j
  obtain ⟨G,hG,hG0,hbound⟩ := hjets j
  refine ⟨fun k=>G (1+2*k+1),hG.comp_injective (by intro x y h; dsimp at h; omega),
    fun k=>hG0 _,?_⟩
  intro eta heta u hu hi k
  have ht := htube eta heta u (hu.trans_le (min_le_left _ _))
  have hpa := negativeEvenPhysicalParameter_family_analyticAt b ht.1 ht.2.1 ht.2.2.1
  have hsi : ContinuousAt (fun q=>S (curve q)) (u,eta) :=
    Complex.continuous_sinh.continuousAt.comp ht.1.continuousAt.fst
  have heq : (fun q=>lowFullParticle (j+2+k) (curve q)) =ᶠ[𝓝 (u,eta)]
      (fun q=>FormFactors.lowPrefactor (curve q)*independentAngularCoefficient (2*(j+2+k)+1) b (negativeEvenPhysicalParameter b (curve q))) := by
    filter_upwards [ht.1.continuousAt.preimage_mem_nhds (lowDomain_isOpen.mem_nhds (ht.2.2.2.2.mpr hi)),
      hsi.eventually_ne ht.2.1,
      continuousAt_const.eventually_lt (Complex.continuous_im.continuousAt.comp hpa.continuousAt.snd.fst) ht.2.2.1,
      continuousAt_const.eventually_lt (Complex.continuous_im.continuousAt.comp hpa.continuousAt.fst)
        (show 0<(negativeParameter b (curve (u,eta))).im by rw [ht.2.2.2.1]; exact hi)] with q hq hs hb' hi'
    exact lowFullParticle_negative_independent _ hq hs hb' hi'
  rw [(heq.iteratedFDeriv ℂ j).eq_of_nhds]
  have hh := hbound eta heta u (hu.trans_le (min_le_right _ _))
    (show 0<(negativeEvenPhysicalParameter b (curve (u,eta))).1.im by change 0<(negativeParameter b (curve (u,eta))).im; rw [ht.2.2.2.1]; exact hi) (1+2*k+1)
  simpa only [show 2*j+3+(1+2*k+1)=2*(j+2+k)+1 by omega] using hh

end
end IsingBulk.Joint.Transverse
