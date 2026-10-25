import IsingBulk.Joint.Transverse.FamilyPositiveSide
import IsingBulk.Joint.RegularEdges.FamilyParticleRoot

/-! # Exact full physical family identities with one canonical particle root -/
namespace IsingBulk.Joint.Transverse
noncomputable section
open IsingBulk.Joint.RegularEdges IsingBulk.Anisotropic.RegularEdges Set Filter Metric
open scoped Topology

def positiveParticleScale (K : Coupling) : ℂ := S K/positiveParticleRoot K
def positiveHighMultiplier (K : Coupling) : ℂ := FormFactors.highPrefactor K/positiveParticleRoot K

def positiveHighLeading {E : Type*} (n k : ℕ) (b : ℝ) (curve : ℂ × E→Coupling) (eta : E) : ℂ :=
  positiveHighMultiplier (curve (0,eta))*edgeCoefficientLeading n k b
    (fun u=>transferB (curve (u,eta))) (fun u=>positiveParticleScale (curve (u,eta)))

def positiveLowLeading {E : Type*} (n k : ℕ) (b : ℝ) (curve : ℂ × E→Coupling) (eta : E) : ℂ :=
  FormFactors.lowPrefactor (curve (0,eta))*edgeCoefficientLeading n k b
    (fun u=>transferB (curve (u,eta))) (fun u=>positiveParticleScale (curve (u,eta)))

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem positiveHighMultiplier_family_analyticAt {curve : E→Coupling} {x : E}
    (hc : AnalyticAt ℂ curve x) (hK : curve x∈closure highDomain)
    (hp : p (curve x)^2≠1) (hS : S (curve x)≠0) (hB : 0<(transferB (curve x)).im) :
    AnalyticAt ℂ (fun x=>positiveHighMultiplier (curve x)) x :=
  ((highPrefactor_boundary_analyticAt hK hp).comp hc).div
    (positiveParticleRoot_family_analyticAt hc hS hB) (positiveParticleRoot_ne_zero hS hB)

theorem compact_family_positive_high_parity_identity {b : ℝ} (curve : ℂ × E→Coupling)
    {Q : Set E} (hQ : IsCompact Q) (hc : ∀eta∈Q,AnalyticAt ℂ curve (0,eta))
    (hK : ∀eta∈Q,curve (0,eta)∈frontier highDomain)
    (hS : ∀eta∈Q,S (curve (0,eta))≠0) (hp : ∀eta∈Q,p (curve (0,eta))^2≠1)
    (hB : ∀eta∈Q,0<(transferB (curve (0,eta))).im) (hb : |b|<1)
    (hn : ∀eta∈Q,∀ᶠu : ℂ in 𝓝 0,positiveParameter b (curve (u,eta))=u) :
    ∃δ : ℝ,0<δ ∧ ∀eta∈Q,∀u : ℂ,‖u‖<δ → 0<u.im →
      FormFactors.highNormalizedBulk (curve (u,eta))=
        positiveHighMultiplier (curve (u,eta))*paritySeries 0 b
          (fun v=>transferB (curve (v,eta))) (fun v=>positiveParticleScale (curve (v,eta))) u := by
  obtain ⟨r,hr,htube⟩ := compact_family_positive_high_tube curve hQ hc hK hS hp hB hb hn
  obtain ⟨δ,hδ,hid⟩ := compact_family_positive_high_physical_identity curve hQ hc hK hS hp hB hb hr
    (fun eta heta u hu=>(htube eta heta u hu).2.2.2.1)
  refine ⟨min r δ,lt_min hr hδ,?_⟩
  intro eta heta u hu hi
  have ht := htube eta heta u (hu.trans_le (min_le_left _ _))
  have hR : positiveParticleRoot (curve (u,eta))≠0 := positiveParticleRoot_ne_zero ht.2.1 ht.2.2.1
  rw [(hid eta heta u (hu.trans_le (min_le_right _ _)) hi).2]
  have he := oddSeries_rescale b (fun v=>transferB (curve (v,eta)))
    (fun v=>S (curve (v,eta))) (fun v=>positiveParticleRoot (curve (v,eta)))
    (fun v=>p (curve (v,eta))) u (positiveParticleRoot_sq _)
  change _=FormFactors.highPrefactor (curve (u,eta))/positiveParticleRoot (curve (u,eta))*_
  simp only [positiveParticleScale]
  rw [he]
  field_simp

theorem compact_family_positive_low_parity_identity {b : ℝ} (curve : ℂ × E→Coupling)
    {Q : Set E} (hQ : IsCompact Q) (hc : ∀eta∈Q,AnalyticAt ℂ curve (0,eta))
    (hK : ∀eta∈Q,curve (0,eta)∈frontier lowDomain)
    (hS : ∀eta∈Q,S (curve (0,eta))≠0) (hp : ∀eta∈Q,p (curve (0,eta))^2≠1)
    (hB : ∀eta∈Q,0<(transferB (curve (0,eta))).im) (hb : |b|<1)
    (hn : ∀eta∈Q,∀ᶠu : ℂ in 𝓝 0,positiveParameter b (curve (u,eta))=u) :
    ∃δ : ℝ,0<δ ∧ ∀eta∈Q,∀u : ℂ,‖u‖<δ → 0<u.im →
      FormFactors.lowNormalizedBulk (curve (u,eta))=
        FormFactors.lowPrefactor (curve (u,eta))*paritySeries 1 b
          (fun v=>transferB (curve (v,eta))) (fun v=>positiveParticleScale (curve (v,eta))) u := by
  obtain ⟨r,hr,htube⟩ := compact_family_positive_low_tube curve hQ hc hK hS hp hB hb hn
  obtain ⟨δ,hδ,hid⟩ := compact_family_positive_low_physical_identity curve hQ hc hK hS hp hB hb hr
    (fun eta heta u hu=>(htube eta heta u hu).2.2.2.1)
  refine ⟨δ,hδ,?_⟩
  intro eta heta u hu hi
  rw [(hid eta heta u hu hi).2]
  congr 1
  exact (evenSeries_rescale b (fun v=>transferB (curve (v,eta)))
    (fun v=>S (curve (v,eta))) (fun v=>positiveParticleRoot (curve (v,eta)))
    (fun v=>p (curve (v,eta))) u (positiveParticleRoot_sq _)).symm

end
end IsingBulk.Joint.Transverse
