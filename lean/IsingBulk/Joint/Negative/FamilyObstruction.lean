import IsingBulk.Joint.Negative.FamilyCurveRanges
import IsingBulk.Anisotropic.NegativeDominance.PrimeNegativePhase

/-! The negative-odd compact complex-family endpoint. This proposition records
actual complete coefficient growth, not assumptions about model ranges. -/
namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter IsingBulk.Anisotropic
open IsingBulk.Anisotropic.NegativeDominance
open scoped Topology
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Literal full boundary Taylor coefficients have radius zero, with one common
selected-growth threshold for the compact parameter set, and every common
geometric coefficient bound fails beyond one common particle threshold.
The selected integer order may depend on the complex parameter. -/
def CompactNegativeCoefficientObstruction (curve : ℂ × E→Coupling)
    (amp : ℂ × E→ℂ) (Q : Set E) : Prop :=
  (∀eta∈Q,(FormalMultilinearSeries.ofScalars ℂ
    (negativePaperCoefficient (fun t=>curve (t,eta)) (familyMember amp eta))).radius=0) ∧
  ∃p0 : ℕ,0<p0 ∧ Odd p0 ∧
    (∃G : ℝ,∃N : ℕ,∀eta∈Q,∀ell : ℕ,N≤resonantParticle p0 ell → ∃j : ℕ,
      lowerCrossingOrder (resonantParticle p0 ell)-1<(j:ℝ) ∧
      (j:ℝ)≤upperCrossingOrder (resonantParticle p0 ell) ∧ resonantParticle p0 ell≤j ∧
      Real.exp ((j:ℝ)*(2*Real.log (resonantParticle p0 ell)-G))/2≤
        ‖negativePaperCoefficient (fun t=>curve (t,eta)) (familyMember amp eta) j‖) ∧
    ∀r : ℝ,0<r → ∀Cbound : ℝ,∃N : ℕ,∀eta∈Q,∀ell : ℕ,N≤resonantParticle p0 ell → ∃j : ℕ,
      lowerCrossingOrder (resonantParticle p0 ell)-1<(j:ℝ) ∧
      (j:ℝ)≤upperCrossingOrder (resonantParticle p0 ell) ∧ resonantParticle p0 ell≤j ∧
      Cbound<‖negativePaperCoefficient (fun t=>curve (t,eta)) (familyMember amp eta) j‖*r^j

/-- Actual normalized jointly holomorphic negative-edge families satisfy the
full common compact-family conclusion. There are no normal-form, transport,
coefficient-range, coefficient-bound or Taylor-radius hypotheses. -/
theorem compact_normalized_negative_family_obstruction
    {Q : Set E} (curve : ℂ × E→Coupling) (amp : ℂ × E→ℂ) {b : ℝ}
    (hQ : IsCompact Q) (hc : ∀eta∈Q,AnalyticAt ℂ curve (0,eta))
    (ha : ∀eta∈Q,AnalyticAt ℂ amp (0,eta))
    (hS : ∀eta∈Q,S (curve (0,eta))≠0)
    (hB : ∀eta∈Q,(transferB (curve (0,eta))).im<0)
    (hprime : b∈primePhaseCosines)
    (he : ∀eta∈Q,∀ᶠt : ℂ in 𝓝 0,transferC (curve (t,eta))+transferB (curve (t,eta))=
      (b:ℂ)+transferB (curve (t,eta))*t)
    (hsq : ∀eta∈Q,∀ᶠt : ℂ in 𝓝 0,amp (t,eta)^2=p (curve (t,eta))) :
    CompactNegativeCoefficientObstruction curve amp Q := by
  obtain ⟨p0,phi,hp,hpo,hphi0,hphipi,hphi,hcos,hphase,hres⟩ := exists_prime_negative_phase hprime
  obtain ⟨a,E0,D,C,haR,_hE,hD,hranges⟩ := compact_normalized_negative_family_ranges curve amp
    hQ hc ha hS hB phi hphi0 hphipi hphi
    (by simpa only [hcos] using he) hsq p0 hp.two_le hpo
    (by simpa only [hcos] using hphase) (fun m hm=>hres (2*m+1) hm)
  let coeff : E→ℕ→ℂ := fun eta=>negativePaperCoefficient (fun t=>curve (t,eta)) (familyMember amp eta)
  let B := familyPaperB curve
  let rootB := familyPaperRoot curve amp
  have hn := fun eta heta=>familyPaper_nonzero (hS eta heta) (hB eta heta) (hsq eta heta)
  have hBa : ∀eta∈Q,AnalyticAt ℂ B (0,eta) :=
    fun eta heta=>familyPaperB_analyticAt (hc eta heta) (hS eta heta)
  have hBn : ∀eta∈Q,B (0,eta)≠0 := fun eta heta=>(hn eta heta).2.1
  have hra : ∀eta∈Q,AnalyticAt ℂ rootB (0,eta) :=
    fun eta heta=>familyPaperRoot_analyticAt (hc eta heta) (ha eta heta) (hS eta heta)
  have hrn : ∀eta∈Q,rootB (0,eta)≠0 := fun eta heta=>(hn eta heta).2.2
  have hrsq : ∀eta∈Q,∀ᶠt : ℂ in 𝓝 0,rootB (t,eta)^2=B (t,eta) :=
    fun eta heta=>familyPaper_square_germ (hc eta heta) (hS eta heta) (hsq eta heta)
  have hrad := compact_family_complete_coefficient_radius_zero coeff B rootB phi hQ
    hBa hBn hra hrn hrsq hphi p0 hp.pos hpo haR hD (actualMiddleErrorScale_tendsto_zero E0) hranges
  have hsel := compact_family_complete_coefficient_selected_growth coeff B rootB phi hQ
    hBa hBn hra hrn hrsq hphi p0 hp.pos hpo haR hD (actualMiddleErrorScale_tendsto_zero E0) hranges
  have hunbounded := compact_family_complete_coefficient_uniform_unbounded coeff B rootB phi hQ
    hBa hBn hra hrn hrsq hphi p0 hp.pos hpo haR hD (actualMiddleErrorScale_tendsto_zero E0) hranges
  refine ⟨hrad,p0,hp.pos,hpo,?_,hunbounded⟩
  obtain ⟨G,N,hsel⟩ := hsel
  refine ⟨G,N,?_⟩
  intro eta heta ell hell
  obtain ⟨j,hjl,hjh,hnj,_hdom,hgrowth⟩ := hsel eta heta ell hell
  exact ⟨j,hjl,hjh,hnj,hgrowth⟩

end
end IsingBulk.Joint.Negative
