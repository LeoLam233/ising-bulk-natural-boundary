import IsingBulk.Anisotropic.NegativeDominance.ActualMiddleParticle
import IsingBulk.Joint.Negative.ModelData
import IsingBulk.Joint.Negative.CentralKernelDecomposition

noncomputable section
open IsingBulk.Anisotropic IsingBulk.Anisotropic.NegativeDominance
namespace IsingBulk.Joint.Negative
open IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.First IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.Anisotropic.NegativeNormalForm IsingBulk.Anisotropic.RegularEdges
open Set MeasureTheory Filter
open scoped Topology BigOperators
set_option maxHeartbeats 3000000

/-- The literal resonant middle particle coefficient: central exact model,
all higher windings, and the actual analytic remainder. -/
theorem exists_actual_middle_particle_bound (B rootB : ℂ→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hp : 0<phi) (hpi : phi<Real.pi)
    (hB : AnalyticAt ℂ B 0) (hB0 : B 0≠0)
    (hrB : AnalyticAt ℂ rootB 0) (hr0 : rootB 0≠0)
    (hsq : ∀ᶠt in 𝓝 (0:ℂ),rootB t^2=B t)
    (curve : ℂ→Coupling) (amp : ℂ→ℂ) (hcurve : AnalyticAt ℂ curve 0) (hA : AnalyticAt ℂ amp 0)
    (hS : S (curve 0)≠0)
    (hedge : A (curve 0)+T (curve 0)=(Real.cos phi:ℂ)*S (curve 0))
    (hb : |Real.cos phi|<1) (hBi : 0<(-T (curve 0)/S (curve 0)).im)
    (hchart : ∀ᶠt in 𝓝 (0:ℂ),S (curve t)≠0 ∧
      B t=T (curve t)/S (curve t) ∧
      transferC (curve t)+transferB (curve t)=(Real.cos phi:ℂ)+B t*t ∧
      amp t^2=p (curve t) ∧ amp t/S (curve t)=rootB t)
    (houter : ∀s : ℝ,0<s → ∃g D : ℝ,0<g ∧ 0<D ∧ ∀m j : ℕ,
      ‖∫v in physicalOuterRegion (2*m) s,physicalDensityTaylor (2*m) curve amp j v‖≤
        gaussianEnvelope g D (2*m+1) j) :
    ∃E g D : ℝ,0<E ∧ 0<g ∧ 0<D ∧ ∀ᶠj : ℕ in atTop,∀m : ℕ,
      Real.log j<(2*m+1:ℕ) → ((2*m+1:ℕ):ℝ)^2≤(j:ℝ)/Real.sqrt (Real.log j) →
      Complex.exp (((2*m+1:ℕ):ℂ)*((phi:ℂ)*Complex.I))=1 →
      ‖negativePaperParticleCoefficient curve amp m j-physicalModel B rootB phi (2*m+1) j‖≤
        (E*middleDensityScale j+Real.exp (-(j:ℝ)*Real.log 2/4))*
          ‖physicalModel B rootB phi (2*m+1) j‖+gaussianEnvelope g D (2*m+1) j := by
  obtain ⟨R,r,C,hR,hr,_hC,hRr,hfactory⟩ := exists_winding_witness_factory B phi hphi hB hB0
  obtain ⟨R0,rho,c,sigma,K,M,_hrho,hc,hsigma,hK,hM,hdec⟩ :=
    physical_central_kernel_decomposition B rootB phi hphi hp hpi hB hB0 hrB r C R hr hR (by linarith)
  obtain ⟨rhoW,hrhoW,N0,hwind⟩ := actual_noncentral_winding_middle_sum B rootB phi hphi hB hrB hB0 hr0 r C hr
  obtain ⟨sigmaC,hsigmaC,hcentral⟩ := exists_actual_central_fixed_cutoff B rootB phi hphi hB hB0 hrB hr0 hsq
  obtain ⟨s,hs,hsmax⟩ := exists_between (lt_min hsigma (lt_min hsigmaC (lt_min (sq_pos_of_pos hR) (sq_pos_of_pos hrhoW))))
  rcases lt_min_iff.mp hsmax with ⟨hss,hsmax⟩
  rcases lt_min_iff.mp hsmax with ⟨hsc,hsmax⟩
  rcases lt_min_iff.mp hsmax with ⟨hsR,hsW⟩
  obtain ⟨E,gc,Dc,hE,hgc,hDc,hcentral⟩ := hcentral s hs hsc
  obtain ⟨m0,hm0⟩ := eventually_atTop.1 hcentral
  obtain ⟨go,Do,hgo,hDo,houter⟩ := houter s hs
  obtain ⟨gr,Dr,hgr,hDr,hrem⟩ := actual_winding_remainder_sum_gaussian B rootB R0 phi hphi K M c sigma hK hM hc hsigma
  let g := min gc (min go gr)
  let D := max Dc (max Do Dr+Real.log 2)+Real.log 2
  refine ⟨E,g,D,hE,lt_min hgc (lt_min hgo hgr),?_,?_⟩
  · dsimp [D]
    have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
    linarith [le_max_left Dc (max Do Dr+Real.log 2)]
  have hlog : Tendsto (fun j : ℕ=>Real.log (j:ℝ)) atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hwind,eventually_middle_density_small hE.le (by norm_num : (0:ℝ)<1),
    hlog.eventually_ge_atTop (2*(max m0 (max N0 1):ℕ)+1),eventually_ge_atTop (2:ℕ)] with j hw hdens hjlog hj2
  intro m hlo hcut hres
  have hm : max m0 (max N0 1)≤m := by
    have hh : (2*(max m0 (max N0 1):ℕ)+1:ℝ)<(2*m+1:ℕ) := hjlog.trans_lt hlo
    have hn : 2*(max m0 (max N0 1))+1<2*m+1 := by exact_mod_cast hh
    omega
  have hmm0 : m0≤m := (le_max_left _ _).trans hm
  have hmN : N0≤2*m := by have hh := (le_max_left N0 1).trans ((le_max_right m0 _).trans hm); omega
  have hm1 : 1≤m := (le_max_right N0 1).trans ((le_max_right m0 _).trans hm)
  obtain ⟨P,⟨J⟩⟩ := hfactory m s hsR.le
  have hdec' := hdec m s hss curve amp hcurve hA hS hedge hb hBi hchart hres P J j
  have hc' := hm0 m hmm0 j (hdens (2*m+1) hcut).1
  have hw' := hw m hmN hm1 hcut s hsW.le P
  have hr' := hrem m j (windingMean (2*m)) s hss.le (fun k hk=>(P k hk).T)
    (noncentralWindingIndices m) (fun k _ hk=>hdec'.2 k hk)
  have ho' := houter m j
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
