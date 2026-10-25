import IsingBulk.Joint.Transverse.FamilyPhysicalLeading
import IsingBulk.Joint.Transverse.FamilyParticleIdentity
import IsingBulk.Joint.RegularEdges.FamilyWeightedTails

/-! # Literal complete physical differentiated particle tails on arbitrary families -/
namespace IsingBulk.Joint.Transverse
noncomputable section
open IsingBulk.Joint.RegularEdges IsingBulk.Anisotropic.RegularEdges Set Filter Metric
open scoped Topology
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

private theorem actual_particle_tails_of_uniform_identity {b : ℝ} (B V A : ℂ × E→ℂ)
    (P : ℕ→ℂ × E→ℂ) (e : ℕ) {Q : Set E}
    (hb : |b|<1) (hQ : IsCompact Q) (hBa : ∀eta∈Q,AnalyticAt ℂ B (0,eta))
    (hVa : ∀eta∈Q,AnalyticAt ℂ V (0,eta)) (hAa : ∀eta∈Q,AnalyticAt ℂ A (0,eta))
    (hB : ∀eta∈Q,0<(B (0,eta)).im) (hV0 : ∀eta∈Q,V (0,eta)≠0)
    {r : ℝ} (hr : 0<r)
    (hid : ∀eta∈Q,∀u : ℂ,‖u‖<r → 0<u.im → ∀m : ℕ,
      P m (u,eta)=A (u,eta)*angularCoefficient (2*m+e) b (fun t=>B (t,eta)) (fun t=>V (t,eta)) u) :
    ∃δ : ℝ,0<δ ∧ ∀j : ℕ,∃G : ℕ→ℝ,Summable G ∧ (∀k,0≤G k) ∧
      ∀eta∈Q,∀u : ℂ,‖u‖<δ → 0<u.im → ∀k : ℕ,
      ‖iteratedDeriv j (fun t=>P (j+2+k) (t,eta)) u‖≤G k := by
  obtain ⟨δ,hδ,hjets⟩ := compact_prefactored_family_coefficient_tails B V A hb hQ hBa hVa hAa hB hV0
  refine ⟨min r δ,lt_min hr hδ,?_⟩
  intro j
  obtain ⟨G,hG,hG0,hbound⟩ := hjets j
  refine ⟨fun k=>G (1+2*k+e),hG.comp_injective (by intro x y h; dsimp at h; omega),
    fun k=>hG0 _,?_⟩
  intro eta heta u hu hi k
  have heq : (fun t=>P (j+2+k) (t,eta)) =ᶠ[𝓝 u]
      (fun t=>A (t,eta)*angularCoefficient (2*(j+2+k)+e) b (fun v=>B (v,eta)) (fun v=>V (v,eta)) t) := by
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds (hu.trans_le (min_le_left _ _)),
      (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hi] with v hv hvi
    exact hid eta heta v hv hvi _
  rw [heq.iteratedDeriv_eq j]
  have hh := hbound eta heta u (hu.trans_le (min_le_right _ _)) hi (1+2*k+e)
  simpa only [show 2*j+3+(1+2*k+e)=2*(j+2+k)+e by omega] using hh

/-- One common radius before every derivative order for the actual positive high
particle series. It retains every tail particle, onsite term and physical prefactor. -/
theorem positive_high_compact_family_particle_tails {b : ℝ} (curve : ℂ × E→Coupling)
    {Q : Set E} (hQ : IsCompact Q) (hc : ∀eta∈Q,AnalyticAt ℂ curve (0,eta))
    (hK : ∀eta∈Q,curve (0,eta)∈frontier highDomain)
    (hS : ∀eta∈Q,S (curve (0,eta))≠0) (hp : ∀eta∈Q,p (curve (0,eta))^2≠1)
    (hB : ∀eta∈Q,0<(transferB (curve (0,eta))).im) (hb : |b|<1)
    (hn : ∀eta∈Q,∀ᶠu : ℂ in 𝓝 0,positiveParameter b (curve (u,eta))=u) :
    ∃δ : ℝ,0<δ ∧ ∀j : ℕ,∃G : ℕ→ℝ,Summable G ∧ (∀k,0≤G k) ∧
      ∀eta∈Q,∀u : ℂ,‖u‖<δ → 0<u.im → ∀k : ℕ,
      ‖iteratedDeriv j (fun t=>highFullParticle (j+2+k) (curve (t,eta))) u‖≤G k := by
  obtain ⟨r,hr,htube⟩ := compact_family_positive_high_tube curve hQ hc hK hS hp hB hb hn
  apply actual_particle_tails_of_uniform_identity
    (fun q=>transferB (curve q)) (fun q=>positiveParticleScale (curve q)) (fun q=>positiveHighMultiplier (curve q))
    (fun m q=>highFullParticle m (curve q)) 0 hb hQ
    (fun eta heta=>transferB_family_analyticAt (hc eta heta) (hS eta heta))
    (fun eta heta=>positiveParticleScale_family_analyticAt (hc eta heta) (hS eta heta) (hB eta heta))
    (fun eta heta=>positiveHighMultiplier_family_analyticAt (hc eta heta) (hK eta heta).1 (hp eta heta) (hS eta heta) (hB eta heta)) hB
    (fun eta heta=>div_ne_zero (hS eta heta) (positiveParticleRoot_ne_zero (hS eta heta) (hB eta heta))) hr
  intro eta heta u hu hi m
  have ht := htube eta heta u hu
  exact highFullParticle_positive_model m (curve:=fun t=>curve (t,eta)) (ht.2.2.2.2.mpr hi)
    ht.2.1 ht.2.2.1 ht.2.2.2.1 hi

/-- One common radius before every derivative order for the actual positive low
particle series. It retains every tail particle, onsite term and physical prefactor. -/
theorem positive_low_compact_family_particle_tails {b : ℝ} (curve : ℂ × E→Coupling)
    {Q : Set E} (hQ : IsCompact Q) (hc : ∀eta∈Q,AnalyticAt ℂ curve (0,eta))
    (hK : ∀eta∈Q,curve (0,eta)∈frontier lowDomain)
    (hS : ∀eta∈Q,S (curve (0,eta))≠0) (hp : ∀eta∈Q,p (curve (0,eta))^2≠1)
    (hB : ∀eta∈Q,0<(transferB (curve (0,eta))).im) (hb : |b|<1)
    (hn : ∀eta∈Q,∀ᶠu : ℂ in 𝓝 0,positiveParameter b (curve (u,eta))=u) :
    ∃δ : ℝ,0<δ ∧ ∀j : ℕ,∃G : ℕ→ℝ,Summable G ∧ (∀k,0≤G k) ∧
      ∀eta∈Q,∀u : ℂ,‖u‖<δ → 0<u.im → ∀k : ℕ,
      ‖iteratedDeriv j (fun t=>lowFullParticle (j+2+k) (curve (t,eta))) u‖≤G k := by
  obtain ⟨r,hr,htube⟩ := compact_family_positive_low_tube curve hQ hc hK hS hp hB hb hn
  apply actual_particle_tails_of_uniform_identity
    (fun q=>transferB (curve q)) (fun q=>positiveParticleScale (curve q)) (fun q=>FormFactors.lowPrefactor (curve q))
    (fun m q=>lowFullParticle m (curve q)) 1 hb hQ
    (fun eta heta=>transferB_family_analyticAt (hc eta heta) (hS eta heta))
    (fun eta heta=>positiveParticleScale_family_analyticAt (hc eta heta) (hS eta heta) (hB eta heta))
    (fun eta heta=>(lowPrefactor_boundary_analyticAt (hK eta heta).1 (hp eta heta)).comp (hc eta heta)) hB
    (fun eta heta=>div_ne_zero (hS eta heta) (positiveParticleRoot_ne_zero (hS eta heta) (hB eta heta))) hr
  intro eta heta u hu hi m
  have ht := htube eta heta u hu
  exact lowFullParticle_positive_model m (curve:=fun t=>curve (t,eta)) (ht.2.2.2.2.mpr hi)
    ht.2.1 ht.2.2.1 ht.2.2.2.1 hi

/-- One common radius before every derivative order for the actual negative even low
particle series. It retains every tail particle, onsite term and physical prefactor. -/
theorem negative_even_low_compact_family_particle_tails {b : ℝ} (curve : ℂ × E→Coupling)
    {Q : Set E} (hQ : IsCompact Q) (hc : ∀eta∈Q,AnalyticAt ℂ curve (0,eta))
    (hK : ∀eta∈Q,curve (0,eta)∈frontier lowDomain)
    (hS : ∀eta∈Q,S (curve (0,eta))≠0) (hp : ∀eta∈Q,p (curve (0,eta))^2≠1)
    (hB : ∀eta∈Q,0<(-transferB (curve (0,eta))).im) (hb : |b|<1)
    (hn : ∀eta∈Q,∀ᶠu : ℂ in 𝓝 0,negativeParameter b (curve (u,eta))=u) :
    ∃δ : ℝ,0<δ ∧ ∀j : ℕ,∃G : ℕ→ℝ,Summable G ∧ (∀k,0≤G k) ∧
      ∀eta∈Q,∀u : ℂ,‖u‖<δ → 0<u.im → ∀k : ℕ,
      ‖iteratedDeriv j (fun t=>lowFullParticle (j+2+k) (curve (t,eta))) u‖≤G k := by
  obtain ⟨r,hr,htube⟩ := compact_family_negative_low_tube curve hQ hc hK hS hp hB hb hn
  apply actual_particle_tails_of_uniform_identity
    (fun q=>-transferB (curve q)) (fun q=>negativeEvenParticleScale (curve q)) (fun q=>FormFactors.lowPrefactor (curve q))
    (fun m q=>lowFullParticle m (curve q)) 1 hb hQ
    (fun eta heta=>(transferB_family_analyticAt (hc eta heta) (hS eta heta)).neg)
    (fun eta heta=>negativeEvenParticleScale_family_analyticAt (hc eta heta) (hS eta heta) (hB eta heta))
    (fun eta heta=>(lowPrefactor_boundary_analyticAt (hK eta heta).1 (hp eta heta)).comp (hc eta heta)) hB
    (fun eta heta=>div_ne_zero (mul_ne_zero Complex.I_ne_zero (hS eta heta)) (negativeEvenParticleRoot_ne_zero (hS eta heta) (hB eta heta))) hr
  intro eta heta u hu hi m
  have ht := htube eta heta u hu
  exact lowFullParticle_negative_even_model m (curve:=fun t=>curve (t,eta)) (ht.2.2.2.2.mpr hi)
    ht.2.1 ht.2.2.1 ht.2.2.2.1 hi

end
end IsingBulk.Joint.Transverse
