import IsingBulk.Joint.Negative.FamilyWindingFactory
import IsingBulk.Joint.Negative.FamilyWindingSums
import IsingBulk.Joint.Negative.FamilyCentralFixedCutoff
import IsingBulk.Joint.Negative.FamilyRemainderSum
import IsingBulk.Joint.Negative.FamilyDominanceData
import IsingBulk.Anisotropic.NegativeDominance.ActualHighParticle
import IsingBulk.Joint.Negative.ModelData
import IsingBulk.Joint.Negative.FamilyResidueDecomposition

noncomputable section
open IsingBulk.Anisotropic IsingBulk.Anisotropic.NegativeDominance
namespace IsingBulk.Joint.Negative
open IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.First NegativeNormalForm NegativeCycles RegularEdges
open Set MeasureTheory Filter
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
set_option maxHeartbeats 1000000

/-- The actual resonant physical coefficient has the complete high-range pole
entropy plus a sharp Gaussian remainder. All winding witnesses, the common
cutoff and pole estimates are constructed internally; only the actual outer
integral estimate is supplied by the independent outer boundary theorem. -/
theorem compact_family_high_particle_bound (B rootB : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hp : 0<phi) (hpi : phi<Real.pi)
    {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta)) (hB0 : ∀eta∈Q,B (0,eta)≠0) (hrB : ∀eta∈Q,AnalyticAt ℂ rootB (0,eta))
    (curve : E→ℂ→Coupling) (amp : E→ℂ→ℂ)
    (hcurve : ∀eta∈Q,AnalyticAt ℂ (curve eta) 0) (hA : ∀eta∈Q,AnalyticAt ℂ (amp eta) 0)
    (hS : ∀eta∈Q,S (curve eta 0)≠0)
    (hedge : ∀eta∈Q,A (curve eta 0)+T (curve eta 0)=(Real.cos phi:ℂ)*S (curve eta 0))
    (hBi : ∀eta∈Q,0<(-T (curve eta 0)/S (curve eta 0)).im)
    (hchart : ∀eta∈Q,∀ᶠt in 𝓝 (0:ℂ), S (curve eta t)≠0 ∧
      B (t,eta)=T (curve eta t)/S (curve eta t) ∧
      transferC (curve eta t)+transferB (curve eta t)=(Real.cos phi:ℂ)+B (t,eta)*t ∧
      amp eta t^2=p (curve eta t) ∧ amp eta t/S (curve eta t)=rootB (t,eta))
    (houter : ∀s : ℝ,0<s → ∃g D : ℝ,0<g ∧ 0<D ∧ ∀eta∈Q,∀m j : ℕ,
      ‖∫v in physicalOuterRegion (2*m) s,physicalDensityTaylor (2*m) (curve eta) (amp eta) j v‖≤
        gaussianEnvelope g D (2*m+1) j) :
    ∃g D Chigh : ℝ,0<g ∧ 0<D ∧ 0<Chigh ∧ ∀eta∈Q,∀m : ℕ,1≤m → ∀j : ℕ,
      Complex.exp (((2*m+1:ℕ):ℂ)*((phi:ℂ)*Complex.I))=1 →
      ‖negativePaperParticleCoefficient (curve eta) (amp eta) m j‖≤
        Real.exp (2*j*Real.log (2*m+1:ℕ)-((2*m+1:ℕ):ℝ)^2/2*Real.log (2*m+1:ℕ)+Chigh*((2*m+1:ℕ):ℝ)^2)+
          gaussianEnvelope g D (2*m+1) j := by
  obtain ⟨R,r,C,hR,hr,_hC,hRr,hfactory⟩ := compact_family_winding_witness_factory B phi hphi hQ hB hB0
  obtain ⟨R₀,ρ,c,σ,K,M,_hρ,hc,hσ,hK,hM,hdecomp⟩ :=
    compact_family_physical_residue_decomposition B rootB phi hphi hp hpi hQ hB hB0 hrB r C R hr hR (by linarith)
  obtain ⟨a,Chigh,ha,hChigh,hhigher⟩ := compact_family_all_winding_high_sum B rootB phi hphi hQ hB hrB hB0 r C hr
  let s := min (σ/2) (min (R^2) (a^2))
  have hs : 0<s := lt_min (half_pos hσ) (lt_min (sq_pos_of_pos hR) (sq_pos_of_pos ha))
  have hsσ : s<σ := (min_le_left _ _).trans_lt (half_lt_self hσ)
  have hsR : s≤R^2 := (min_le_right _ _).trans (min_le_left _ _)
  have hsa : s≤a^2 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨go,Do,hgo,hDo,hout⟩ := houter s hs
  obtain ⟨gr,Dr,hgr,hDr,hrem⟩ := uniform_winding_remainder_sum_gaussian K M c σ hK hM hc hσ
  have hD : 0<max Do Dr+Real.log 2 := by
    have hlog : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
    have hmax := le_max_left Do Dr
    linarith
  refine ⟨min go gr,max Do Dr+Real.log 2,Chigh,lt_min hgo hgr,hD,hChigh,?_⟩
  intro eta heta m hm j hres
  let B := familyMember B eta
  let rootB := familyMember rootB eta
  let curve := curve eta
  let amp := amp eta
  obtain ⟨P,⟨J⟩⟩ := hfactory eta heta m s hsR
  have hb : |Real.cos phi|<1 := (sq_lt_one_iff_abs_lt_one _).mp (by
    nlinarith [Real.sin_sq_add_cos_sq phi,sq_pos_of_ne_zero hphi])
  obtain ⟨heq,hjets⟩ := hdecomp eta heta m s hsσ curve amp (hcurve eta heta) (hA eta heta) (hS eta heta) (hedge eta heta) hb (hBi eta heta) (hchart eta heta) hres P J j
  let pole : ℂ := ∑k : Fin (2*m+2),actualWindingPole B rootB phi hphi m r C s P j k
  let rem : ℂ := ∑k : Fin (2*m+2),if hk : (2*m+1:ℕ)*(windingMean (2*m) k)^2<s then
    iteratedDeriv j (centeredInnerRemainder B rootB phi hphi R₀ m (windingMean (2*m) k) s (P k hk).T) 0/(j.factorial:ℂ) else 0
  have hpole := (norm_sum_le (Finset.univ) (fun k=>actualWindingPole B rootB phi hphi m r C s P j k)).trans
    (hhigher eta heta m hm s hsa P j)
  change ‖pole‖≤_ at hpole
  have hrbound := hrem B rootB R₀ phi hphi m j (windingMean (2*m)) s hsσ.le (fun k hk=>(P k hk).T) Finset.univ
    (fun k _ hk=>hjets k hk)
  change ‖rem‖≤_ at hrbound
  have heq' : negativePaperParticleCoefficient curve amp m j=
      (∫v in physicalOuterRegion (2*m) s,physicalDensityTaylor (2*m) curve amp j v)+(pole+rem) := heq
  rw [heq']
  have hn1 := norm_add_le (∫v in physicalOuterRegion (2*m) s,physicalDensityTaylor (2*m) curve amp j v) (pole+rem)
  have hn2 := norm_add_le pole rem
  have hout' := hout eta heta m j
  have hgadd := gaussianEnvelope_add go gr Do Dr (2*m+1) j
  linarith


end IsingBulk.Joint.Negative
