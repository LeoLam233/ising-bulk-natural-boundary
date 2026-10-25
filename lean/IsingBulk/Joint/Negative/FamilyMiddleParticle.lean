import IsingBulk.Joint.Negative.FamilyWindingFactory
import IsingBulk.Joint.Negative.FamilyWindingSums
import IsingBulk.Joint.Negative.FamilyCentralFixedCutoff
import IsingBulk.Joint.Negative.FamilyRemainderSum
import IsingBulk.Joint.Negative.FamilyDominanceData
import IsingBulk.Anisotropic.NegativeDominance.ActualMiddleParticle
import IsingBulk.Joint.Negative.ModelData
import IsingBulk.Joint.Negative.FamilyCentralKernelDecomposition

noncomputable section
open IsingBulk.Anisotropic IsingBulk.Anisotropic.NegativeDominance
namespace IsingBulk.Joint.Negative
open IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.First IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.Anisotropic.NegativeNormalForm IsingBulk.Anisotropic.RegularEdges
open Set MeasureTheory Filter
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
set_option maxHeartbeats 3000000

/-- The literal resonant middle particle coefficient: central exact model,
all higher windings, and the actual analytic remainder. -/
theorem compact_family_middle_particle_bound (B rootB : ℂ × E→ℂ) (phi : ℝ)
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
        gaussianEnvelope g D (2*m+1) j) :
    ∃E g D : ℝ,0<E ∧ 0<g ∧ 0<D ∧ ∀ᶠj : ℕ in atTop,∀eta∈Q,∀m : ℕ,
      Real.log j<(2*m+1:ℕ) → ((2*m+1:ℕ):ℝ)^2≤(j:ℝ)/Real.sqrt (Real.log j) →
      Complex.exp (((2*m+1:ℕ):ℂ)*((phi:ℂ)*Complex.I))=1 →
      ‖negativePaperParticleCoefficient (curve eta) (amp eta) m j-physicalModel (familyMember B eta) (familyMember rootB eta) phi (2*m+1) j‖≤
        (E*middleDensityScale j+Real.exp (-(j:ℝ)*Real.log 2/4))*
          ‖physicalModel (familyMember B eta) (familyMember rootB eta) phi (2*m+1) j‖+gaussianEnvelope g D (2*m+1) j := by
  obtain ⟨R,r,C,hR,hr,_hC,hRr,hfactory⟩ := compact_family_winding_witness_factory B phi hphi hQ hB hB0
  obtain ⟨R0,rho,c,sigma,K,M,_hrho,hc,hsigma,hK,hM,hdec⟩ :=
    compact_family_physical_central_decomposition B rootB phi hphi hp hpi hQ hB hB0 hrB r C R hr hR (by linarith)
  obtain ⟨rhoW,hrhoW,N0,hwind⟩ := compact_family_noncentral_winding_sum B rootB phi hphi hQ hB hrB hB0 hr0 r C hr
  obtain ⟨sigmaC,hsigmaC,hcentral⟩ := compact_family_central_fixed_cutoff B rootB phi hphi hQ hB hB0 hrB hr0
      (compact_family_square_identity B rootB hQ hB hrB hsq)
  obtain ⟨s,hs,hsmax⟩ := exists_between (lt_min hsigma (lt_min hsigmaC (lt_min (sq_pos_of_pos hR) (sq_pos_of_pos hrhoW))))
  rcases lt_min_iff.mp hsmax with ⟨hss,hsmax⟩
  rcases lt_min_iff.mp hsmax with ⟨hsc,hsmax⟩
  rcases lt_min_iff.mp hsmax with ⟨hsR,hsW⟩
  obtain ⟨E,gc,Dc,hE,hgc,hDc,hcentral⟩ := hcentral s hs hsc
  obtain ⟨m0,hm0⟩ := eventually_atTop.1 hcentral
  obtain ⟨go,Do,hgo,hDo,houter⟩ := houter s hs
  obtain ⟨gr,Dr,hgr,hDr,hrem⟩ := uniform_winding_remainder_sum_gaussian K M c sigma hK hM hc hsigma
  let g := min gc (min go gr)
  let D := max Dc (max Do Dr+Real.log 2)+Real.log 2
  refine ⟨E,g,D,hE,lt_min hgc (lt_min hgo hgr),?_,?_⟩
  · dsimp [D]
    have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
    linarith [le_max_left Dc (max Do Dr+Real.log 2)]
  have hlog : Tendsto (fun j : ℕ=>Real.log (j:ℝ)) atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hwind,eventually_middle_density_small hE.le (by norm_num : (0:ℝ)<1),
    hlog.eventually_ge_atTop (2*(max m0 (max N0 1):ℕ)+1),eventually_ge_atTop (2:ℕ)] with j hw hdens hjlog hj2
  intro eta heta m hlo hcut hres
  let B := familyMember B eta
  let rootB := familyMember rootB eta
  let curve := curve eta
  let amp := amp eta
  have hm : max m0 (max N0 1)≤m := by
    have hh : (2*(max m0 (max N0 1):ℕ)+1:ℝ)<(2*m+1:ℕ) := hjlog.trans_lt hlo
    have hn : 2*(max m0 (max N0 1))+1<2*m+1 := by exact_mod_cast hh
    omega
  have hmm0 : m0≤m := (le_max_left _ _).trans hm
  have hmN : N0≤2*m := by have hh := (le_max_left N0 1).trans ((le_max_right m0 _).trans hm); omega
  have hm1 : 1≤m := (le_max_right N0 1).trans ((le_max_right m0 _).trans hm)
  obtain ⟨P,⟨J⟩⟩ := hfactory eta heta m s hsR.le
  have hdec' := hdec eta heta m s hss curve amp (hcurve eta heta) (hA eta heta) (hS eta heta) (hedge eta heta) hb (hBi eta heta) (hchart eta heta) hres P J j
  have hc' := hm0 m hmm0 eta heta j (hdens (2*m+1) hcut).1
  have hw' := hw eta heta m hmN hm1 hcut s hsW.le P
  have hr' := hrem B rootB R0 phi hphi m j (windingMean (2*m)) s hss.le (fun k hk=>(P k hk).T)
    (noncentralWindingIndices m) (fun k _ hk=>hdec'.2 k hk)
  have ho' := houter eta heta m j
  have hws : ‖∑k∈noncentralWindingIndices m,actualWindingPole B rootB phi hphi m r C s P j k‖≤
      Real.exp (-(j:ℝ)*Real.log 2/4)*‖physicalModel B rootB phi (2*m+1) j‖ :=
    (norm_sum_le _ _).trans hw'
  have htri : ‖negativePaperParticleCoefficient curve amp m j-physicalModel B rootB phi (2*m+1) j‖≤
      ‖2*(iteratedDeriv j (centeredKernelIntegral B rootB phi hphi m (Real.pi/(2*m+1:ℕ)) s) 0/(j.factorial:ℂ))-
        physicalModel B rootB phi (2*m+1) j‖+
      ‖∑k∈noncentralWindingIndices m,actualWindingPole B rootB phi hphi m r C s P j k‖+
      (‖∫v in physicalOuterRegion (2*m) s,physicalDensityTaylor (2*m) curve amp j v‖+
        ‖∑k∈noncentralWindingIndices m,if hk : (2*m+1:ℕ)*(windingMean (2*m) k)^2<s then
          iteratedDeriv j (centeredInnerRemainder B rootB phi hphi R0 m (windingMean (2*m) k) s (P k hk).T) 0/(j.factorial:ℂ) else 0‖) := by
    change ‖_/(j.factorial:ℂ)-_‖≤_
    rw [hdec'.1]
    rw [show ∀a b c d e : ℂ,a+b+(c+d)-e=(a-e)+b+(c+d) by intros; ring]
    exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
  have hsmall := mul_le_mul_of_nonneg_left (density_scale_le_middle (by omega) hcut) hE.le
  have hsmall' := mul_le_mul_of_nonneg_right hsmall (norm_nonneg (physicalModel B rootB phi (2*m+1) j))
  have hgadd := gaussianEnvelope_add gc (min go gr) Dc (max Do Dr+Real.log 2) (2*m+1) j
  have hgadd' := gaussianEnvelope_add go gr Do Dr (2*m+1) j
  dsimp only [gaussianEnvelope] at hgadd hgadd'
  dsimp only [gaussianEnvelope,g,D]
  dsimp only [gaussianEnvelope] at hr' ho' hc'
  nlinarith [hc',hws,htri,hsmall',hgadd,hgadd',hr',ho']

end IsingBulk.Joint.Negative
