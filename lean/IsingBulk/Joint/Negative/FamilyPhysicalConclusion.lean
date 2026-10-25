import IsingBulk.Joint.Negative.FamilyNormalizedJets
import IsingBulk.Joint.Negative.FamilyObstruction
import IsingBulk.Anisotropic.Geometry.PrimeOrientation

/-! The complete compact negative family conclusion, including a common
physical inward neighborhood and uniform boundary jets of the literal
normalized susceptibility. All analytic attachments are proved internally. -/
namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic
open scoped Topology
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
/-- Restricting the compact parameter set preserves every common growth
constant and threshold of the actual complete coefficient obstruction. -/
theorem CompactNegativeCoefficientObstruction.mono
    {curve : ℂ × E→Coupling} {amp : ℂ × E→ℂ} {Q R : Set E}
    (h : CompactNegativeCoefficientObstruction curve amp Q) (hRQ : R⊆Q) :
    CompactNegativeCoefficientObstruction curve amp R := by
  obtain ⟨hrad,p0,hp,hodd,⟨G,N,hsel⟩,hunbounded⟩ := h
  refine ⟨fun eta heta=>hrad eta (hRQ heta),p0,hp,hodd,
    ⟨G,N,fun eta heta=>hsel eta (hRQ heta)⟩,?_⟩
  intro r hr C
  obtain ⟨N,hN⟩ := hunbounded r hr C
  exact ⟨N,fun eta heta=>hN eta (hRQ heta)⟩

/-- The actual physical attachment: a common inward high-domain tube and
uniform limits of every complete weighted and literal normalized derivative.
The boundary values are explicitly the true complete odd sum and its physical
analytic-unit Leibniz convolution. -/
def CompactNegativePhysicalAttachment (curve : ℂ × E→Coupling)
    (amp : ℂ × E→ℂ) (Q : Set E) : Prop :=
  (∃r : ℝ,0<r ∧ ∀eta∈Q,∀ε : ℝ,0<ε → ε<r → curve (-(ε:ℂ),eta)∈highDomain) ∧
  (∀j : ℕ,TendstoUniformlyOn
    (fun ε : ℝ=>fun eta=>iteratedDeriv j
      (weightedPhysicalHigh (fun t=>curve (t,eta)) (fun t=>amp (t,eta))) (-(ε:ℂ)))
    (fun eta=>∑'n : ℕ,iteratedDeriv j
      (fun t=>amp (t,eta)^(2*n+1)*continuedAngularCoefficient (2*n) (curve (t,eta))) 0)
    (𝓝[>] 0) Q) ∧
  ∀j : ℕ,TendstoUniformlyOn
    (fun ε : ℝ=>fun eta=>iteratedDeriv j
      (fun t=>FormFactors.highNormalizedBulk (curve (t,eta))) (-(ε:ℂ)))
    (normalizedHighBoundaryJet curve amp j) (𝓝[>] 0) Q

/-- Full common-family obstruction with actual physical boundary-jet
identification, not just a uniform formal coefficient estimate. -/
def CompactNegativePhysicalObstruction (curve : ℂ × E→Coupling)
    (amp : ℂ × E→ℂ) (Q : Set E) : Prop :=
  CompactNegativeCoefficientObstruction curve amp Q ∧
    CompactNegativePhysicalAttachment curve amp Q

/-- Only actual analytic family and boundary geometry are hypotheses. The
common tube, infinite-series derivative passage, uniform boundary approach,
normal-form estimates and complete coefficient growth are all conclusions. -/
theorem compact_negative_high_physical_obstruction {Q : Set E}
    (curve : ℂ × E→Coupling) (amp : ℂ × E→ℂ) {b : ℝ}
    (hQ : IsCompact Q) (hc : ∀eta∈Q,AnalyticAt ℂ curve (0,eta))
    (ha : ∀eta∈Q,AnalyticAt ℂ amp (0,eta))
    (hS : ∀eta∈Q,S (curve (0,eta))≠0)
    (hB : ∀eta∈Q,(transferB (curve (0,eta))).im<0)
    (hK : ∀eta∈Q,curve (0,eta)∈frontier highDomain)
    (hp : ∀eta∈Q,p (curve (0,eta))^2≠1)
    (hprime : b∈primePhaseCosines)
    (he : ∀eta∈Q,∀ᶠt : ℂ in 𝓝 0,transferC (curve (t,eta))+transferB (curve (t,eta))=
      (b:ℂ)+transferB (curve (t,eta))*t)
    (hsq : ∀eta∈Q,∀ᶠt : ℂ in 𝓝 0,amp (t,eta)^2=p (curve (t,eta))) :
    CompactNegativePhysicalObstruction curve amp Q := by
  have hb := abs_lt_one_of_primePhaseCosines hprime
  refine ⟨compact_normalized_negative_family_obstruction curve amp hQ hc ha hS hB hprime he hsq,?_,
    compact_negative_high_weighted_boundary_jets curve amp hQ hc ha hS hB hK hp hb he hsq,
    compact_negative_high_normalized_boundary_jets curve amp hQ hc ha hS hB hK hp hb he hsq⟩
  obtain ⟨r,hr,htube⟩ := compact_negative_high_real_approach curve hQ hc hS hB hK hp hb he
  exact ⟨r,hr,fun eta heta ε hε hεr=>(htube eta heta ε hε hεr).2.2⟩

end
end IsingBulk.Joint.Negative
