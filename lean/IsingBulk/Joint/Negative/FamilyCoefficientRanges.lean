import IsingBulk.Anisotropic.NegativeDominance.ActualPaperRadius
import IsingBulk.Joint.Negative.FamilyMiddleParticle
import IsingBulk.Joint.Negative.FamilyHighParticle
import IsingBulk.Joint.Negative.FamilyDominanceAssembly
import IsingBulk.Joint.Negative.FamilyDominanceUniformGrowth

noncomputable section
open IsingBulk.Anisotropic IsingBulk.Anisotropic.NegativeDominance
namespace IsingBulk.Joint.Negative
open IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.First NegativeNormalForm NegativeCycles RegularEdges
open Set MeasureTheory Filter
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
set_option maxHeartbeats 2000000

/-- Actual complete physical coefficient ranges, derived from the physical
residue decomposition and all-index estimates, not postulated dominance. -/
theorem compact_family_negative_paper_ranges (B rootB : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hp : 0<phi) (hpi : phi<Real.pi)
    {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta)) (hB0 : ∀eta∈Q,B (0,eta)≠0)
    (hrB : ∀eta∈Q,AnalyticAt ℂ rootB (0,eta)) (hr0 : ∀eta∈Q,rootB (0,eta)≠0)
    (hsq : ∀eta∈Q,∀ᶠt in 𝓝 (0:ℂ),rootB (t,eta)^2=B (t,eta))
    (curve : E→ℂ→Coupling) (amp : E→ℂ→ℂ)
    (hcurve : ∀eta∈Q,AnalyticAt ℂ (curve eta) 0) (hA : ∀eta∈Q,AnalyticAt ℂ (amp eta) 0)
    (hS : ∀eta∈Q,S (curve eta 0)≠0)
    (hedge : ∀eta∈Q,A (curve eta 0)+T (curve eta 0)=(Real.cos phi:ℂ)*S (curve eta 0))
    (hb : |Real.cos phi|<1) (hBi : ∀eta∈Q,0<(-T (curve eta 0)/S (curve eta 0)).im)
    (hchart : ∀eta∈Q,∀ᶠt in 𝓝 (0:ℂ),S (curve eta t)≠0 ∧
      B (t,eta)=T (curve eta t)/S (curve eta t) ∧
      transferC (curve eta t)+transferB (curve eta t)=(Real.cos phi:ℂ)+B (t,eta)*t ∧
      amp eta t^2=p (curve eta t) ∧ amp eta t/S (curve eta t)=rootB (t,eta))
    (houter : ∀s : ℝ,0<s → ∃g D : ℝ,0<g ∧ 0<D ∧ ∀eta∈Q,∀m j : ℕ,
      ‖∫v in physicalOuterRegion (2*m) s,physicalDensityTaylor (2*m) (curve eta) (amp eta) j v‖≤
        gaussianEnvelope g D (2*m+1) j)
    (p : ℕ) (hp0 : 0<p) (hpOdd : Odd p)
    (hres : ∀m : ℕ,p∣2*m+1 → Complex.exp (((2*m+1:ℕ):ℂ)*((phi:ℂ)*Complex.I))=1)
    (a Dlow aR CR : ℝ) (ha : 0<a) (hDlow : 0≤Dlow) (haR : 0<aR)
    (hlow : ∀eta∈Q,∀j m,‖negativePaperParticleCoefficient (curve eta) (amp eta) m j‖≤
      Dlow*((2*m+1:ℕ):ℝ)^2*(((2*m+1:ℕ):ℝ)^3/a)^j)
    (hnonres : ∀eta∈Q,∀j m,¬p∣2*m+1 → ‖negativePaperParticleCoefficient (curve eta) (amp eta) m j‖≤
      gaussianEnvelope aR CR (2*m+1) j) :
    ∃E D C : ℝ,0<E ∧ 0<D ∧ ∀ᶠj : ℕ in atTop,∀eta∈Q,
      HasCoefficientRanges (negativePaperCoefficient (curve eta) (amp eta)) (familyMember B eta) (familyMember rootB eta) phi p a D C (actualMiddleErrorScale E) j := by
  obtain ⟨E,gm,Dm,hE,hgm,hDm,hmiddle⟩ := compact_family_middle_particle_bound B rootB phi hphi hp hpi hQ hB hB0 hrB hr0 hsq
    curve amp hcurve hA hS hedge hb hBi hchart houter
  obtain ⟨gh,Dh,Ch,hgh,_hDh,_hCh,hhigh⟩ := compact_family_high_particle_bound B rootB phi hphi hp hpi hQ hB hB0 hrB
    curve amp hcurve hA hS hedge hBi hchart houter
  let g := min gm gh
  let Dg := max Dm Dh
  have hgm' (N j : ℕ) := gaussianEnvelope_mono (min_le_left gm gh) (le_max_left Dm Dh) N j
  have hgh' (N j : ℕ) := gaussianEnvelope_mono (min_le_right gm gh) (le_max_right Dm Dh) N j
  have hm : ∀ᶠj : ℕ in atTop,∀eta∈Q,∀m,p∣2*m+1 → Real.log j<((2*m+1:ℕ):ℝ) →
      ((2*m+1:ℕ):ℝ)^2≤j/Real.sqrt (Real.log j) →
      ‖negativePaperParticleCoefficient (curve eta) (amp eta) m j-physicalModel (familyMember B eta) (familyMember rootB eta) phi (2*m+1) j‖≤
        actualMiddleErrorScale E j*‖physicalModel (familyMember B eta) (familyMember rootB eta) phi (2*m+1) j‖+gaussianEnvelope g Dg (2*m+1) j := by
    filter_upwards [hmiddle] with j hj
    intro eta heta m hm hlo hcut
    exact (hj eta heta m hlo hcut (hres m hm)).trans (add_le_add (le_refl _) (hgm' (2*m+1) j))
  have hh : ∀ᶠj : ℕ in atTop,∀eta∈Q,∀m,p∣2*m+1 → Real.log j<((2*m+1:ℕ):ℝ) →
      (j:ℝ)/Real.sqrt (Real.log j)<((2*m+1:ℕ):ℝ)^2 →
      ‖negativePaperParticleCoefficient (curve eta) (amp eta) m j‖≤
        Real.exp (2*j*Real.log (2*m+1)-((2*m+1:ℕ):ℝ)^2/2*Real.log (2*m+1)+Ch*((2*m+1:ℕ):ℝ)^2)+
        gaussianEnvelope g Dg (2*m+1) j := by
    have hl : Tendsto (fun j : ℕ=>Real.log (j:ℝ)) atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    filter_upwards [hl.eventually_ge_atTop 3] with j hj
    intro eta heta m hm hlo _hcut
    have hm1 : 1≤m := by
      have hn : (3:ℝ)<(2*m+1:ℕ) := hj.trans_lt hlo
      have hn' : 3<2*m+1 := by exact_mod_cast hn
      omega
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using
      (hhigh eta heta m hm1 j (hres m hm)).trans (add_le_add (le_refl _) (hgh' (2*m+1) j))
  obtain ⟨D,C,hD,hranges⟩ := compact_family_negative_paper_ranges_of_particle_estimates curve amp (familyMember B) (familyMember rootB) phi Q hp0 hpOdd ha hDlow
    (lt_min hgm hgh) haR Dg CR Ch (actualMiddleErrorScale E)
    (Filter.Eventually.of_forall (actualMiddleErrorScale_nonneg hE.le)) hlow hnonres hm hh
  exact ⟨E,D,C,hE,hD,hranges⟩


end IsingBulk.Joint.Negative
