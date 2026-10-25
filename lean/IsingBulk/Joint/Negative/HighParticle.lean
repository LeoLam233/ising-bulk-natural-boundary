import IsingBulk.Anisotropic.NegativeDominance.ActualHighParticle
import IsingBulk.Joint.Negative.ModelData
import IsingBulk.Joint.Negative.ResidueDecomposition

noncomputable section
open IsingBulk.Anisotropic IsingBulk.Anisotropic.NegativeDominance
namespace IsingBulk.Joint.Negative
open IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.First NegativeNormalForm NegativeCycles RegularEdges
open MeasureTheory Filter
open scoped Topology BigOperators
set_option maxHeartbeats 1000000

/-- The actual resonant physical coefficient has the complete high-range pole
entropy plus a sharp Gaussian remainder. All winding witnesses, the common
cutoff and pole estimates are constructed internally; only the actual outer
integral estimate is supplied by the independent outer boundary theorem. -/
theorem actual_resonant_high_particle_bound (B rootB : ℂ→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hp : 0<phi) (hpi : phi<Real.pi)
    (hB : AnalyticAt ℂ B 0) (hB0 : B 0≠0) (hrB : AnalyticAt ℂ rootB 0)
    (curve : ℂ→Coupling) (amp : ℂ→ℂ) (hcurve : AnalyticAt ℂ curve 0) (hA : AnalyticAt ℂ amp 0)
    (hS : S (curve 0)≠0)
    (hedge : A (curve 0)+T (curve 0)=(Real.cos phi:ℂ)*S (curve 0))
    (hBi : 0<(-T (curve 0)/S (curve 0)).im)
    (hchart : ∀ᶠt in 𝓝 (0:ℂ), S (curve t)≠0 ∧
      B t=T (curve t)/S (curve t) ∧
      transferC (curve t)+transferB (curve t)=(Real.cos phi:ℂ)+B t*t ∧
      amp t^2=p (curve t) ∧ amp t/S (curve t)=rootB t)
    (houter : ∀s : ℝ,0<s → ∃g D : ℝ,0<g ∧ 0<D ∧ ∀m j : ℕ,
      ‖∫v in physicalOuterRegion (2*m) s,physicalDensityTaylor (2*m) curve amp j v‖≤
        gaussianEnvelope g D (2*m+1) j) :
    ∃g D Chigh : ℝ,0<g ∧ 0<D ∧ 0<Chigh ∧ ∀m : ℕ,1≤m → ∀j : ℕ,
      Complex.exp (((2*m+1:ℕ):ℂ)*((phi:ℂ)*Complex.I))=1 →
      ‖negativePaperParticleCoefficient curve amp m j‖≤
        Real.exp (2*j*Real.log (2*m+1:ℕ)-((2*m+1:ℕ):ℝ)^2/2*Real.log (2*m+1:ℕ)+Chigh*((2*m+1:ℕ):ℝ)^2)+
          gaussianEnvelope g D (2*m+1) j := by
  obtain ⟨R,r,C,hR,hr,_hC,hRr,hfactory⟩ := exists_winding_witness_factory B phi hphi hB hB0
  obtain ⟨R₀,ρ,c,σ,K,M,_hρ,hc,hσ,hK,hM,hdecomp⟩ :=
    physical_resonant_residue_decomposition B rootB phi hphi hp hpi hB hB0 hrB r C R hr hR (by linarith)
  obtain ⟨a,Chigh,ha,hChigh,hhigher⟩ := actual_all_winding_high_sum B rootB phi hphi hB hrB hB0 r C hr
  let s := min (σ/2) (min (R^2) (a^2))
  have hs : 0<s := lt_min (half_pos hσ) (lt_min (sq_pos_of_pos hR) (sq_pos_of_pos ha))
  have hsσ : s<σ := (min_le_left _ _).trans_lt (half_lt_self hσ)
  have hsR : s≤R^2 := (min_le_right _ _).trans (min_le_left _ _)
  have hsa : s≤a^2 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨go,Do,hgo,hDo,hout⟩ := houter s hs
  obtain ⟨gr,Dr,hgr,hDr,hrem⟩ := actual_winding_remainder_sum_gaussian B rootB R₀ phi hphi K M c σ hK hM hc hσ
  have hD : 0<max Do Dr+Real.log 2 := by
    have hlog : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
    have hmax := le_max_left Do Dr
    linarith
  refine ⟨min go gr,max Do Dr+Real.log 2,Chigh,lt_min hgo hgr,hD,hChigh,?_⟩
  intro m hm j hres
  obtain ⟨P,⟨J⟩⟩ := hfactory m s hsR
  have hb : |Real.cos phi|<1 := (sq_lt_one_iff_abs_lt_one _).mp (by
    nlinarith [Real.sin_sq_add_cos_sq phi,sq_pos_of_ne_zero hphi])
  obtain ⟨heq,hjets⟩ := hdecomp m s hsσ curve amp hcurve hA hS hedge hb hBi hchart hres P J j
  let pole : ℂ := ∑k : Fin (2*m+2),actualWindingPole B rootB phi hphi m r C s P j k
  let rem : ℂ := ∑k : Fin (2*m+2),if hk : (2*m+1:ℕ)*(windingMean (2*m) k)^2<s then
    iteratedDeriv j (centeredInnerRemainder B rootB phi hphi R₀ m (windingMean (2*m) k) s (P k hk).T) 0/(j.factorial:ℂ) else 0
  have hpole := (norm_sum_le (Finset.univ) (fun k=>actualWindingPole B rootB phi hphi m r C s P j k)).trans
    (hhigher m hm s hsa P j)
  change ‖pole‖≤_ at hpole
  have hrbound := hrem m j (windingMean (2*m)) s hsσ.le (fun k hk=>(P k hk).T) Finset.univ
    (fun k _ hk=>hjets k hk)
  change ‖rem‖≤_ at hrbound
  have heq' : negativePaperParticleCoefficient curve amp m j=
      (∫v in physicalOuterRegion (2*m) s,physicalDensityTaylor (2*m) curve amp j v)+(pole+rem) := heq
  rw [heq']
  have hn1 := norm_add_le (∫v in physicalOuterRegion (2*m) s,physicalDensityTaylor (2*m) curve amp j v) (pole+rem)
  have hn2 := norm_add_le pole rem
  have hout' := hout m j
  have hgadd := gaussianEnvelope_add go gr Do Dr (2*m+1) j
  linarith


/-- amp noncritical interior phase cannot resonate at the one-particle order. -/
theorem resonant_odd_free_index_pos {phi : ℝ} (hphi : Real.sin phi≠0) {m : ℕ}
    (hres : Complex.exp (((2*m+1:ℕ):ℂ)*((phi:ℂ)*Complex.I))=1) : 1≤m := by
  by_contra hm
  have hm0 : m=0 := by omega
  subst m
  have hh := congrArg Complex.im hres
  simp only [Nat.mul_zero,Nat.zero_add,Nat.cast_one,one_mul,
    Complex.exp_ofReal_mul_I_im,Complex.one_im] at hh
  exact hphi hh

end IsingBulk.Joint.Negative
