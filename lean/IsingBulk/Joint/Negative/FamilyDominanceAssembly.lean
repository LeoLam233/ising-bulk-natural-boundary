import IsingBulk.Anisotropic.NegativeDominance.ParticleEstimatesAssembly
import IsingBulk.Joint.Negative.ParticleAssembly

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter IsingBulk.Anisotropic.NegativeNormalForm
open IsingBulk.Anisotropic.NegativeDominance
open scoped Topology BigOperators
variable {E : Type*}
set_option maxHeartbeats 1600000

theorem family_particle_series_ranges {p : ℕ} (hp : 0<p)
    {a Dlow aG : ℝ} (ha : 0<a) (hDlow : 0≤Dlow) (haG : 0<aG) (CG Chigh : ℝ) :
    ∃D C : ℝ,0<D ∧ ∀ (B rootB : ℂ→ℂ) (phi : ℝ), ∀j L : ℕ,(L : ℝ)≤Real.log j → (0 : ℝ)<j →
      1024≤Real.log (j : ℝ) → 32*Chigh≤Real.log (j : ℝ) →
      ∀eta : ℕ→ℝ,0≤eta j → ∀coeff low mid high err : ℕ→ℂ,
      (∀N,coeff N=low N+particleMiddleModel B rootB phi p j N+mid N+high N+err N) →
      (∀N,L<N → low N=0) →
      (∀N,N≤L → ‖low N‖≤Dlow*(N : ℝ)^2*((N : ℝ)^3/a)^j) →
      (∀N,‖mid N‖≤eta j*‖particleMiddleModel B rootB phi p j N‖) →
      (∀N : ℕ,¬(1≤N ∧ (j : ℝ)/Real.sqrt (Real.log j)≤(N : ℝ)^2) → high N=0) →
      (∀N : ℕ,1≤N → (j : ℝ)/Real.sqrt (Real.log j)≤(N : ℝ)^2 →
        ‖high N‖≤Real.exp (2*j*Real.log N-(N : ℝ)^2/2*Real.log N+Chigh*(N : ℝ)^2)) →
      (∀N,‖err N‖≤Real.exp (-aG*(N : ℝ)^2+((j : ℝ)+1)*Real.log N+CG*((j : ℝ)+1))) →
      Summable coeff ∧ HasCoefficientRanges (fun _=>∑'N,coeff N) B rootB phi p a D C eta j := by
  obtain ⟨DG,hDG,hgauss⟩ := gaussian_log_moment_sum haG CG
  let DH := 1/(1-Real.exp (-1))
  let D := 1+|Dlow|+|DH|+DG
  have hDH : 0<DH := by dsimp [DH]; exact one_div_pos.mpr (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num)))
  have hD : 0<D := by dsimp [D]; positivity
  have hDl : Dlow≤D := by dsimp [D]; linarith [le_abs_self Dlow,abs_nonneg DH]
  have hDh : DH≤D := by dsimp [D]; linarith [le_abs_self DH,abs_nonneg Dlow]
  have hDg : DG≤D := by dsimp [D]; linarith [abs_nonneg Dlow,abs_nonneg DH]
  refine ⟨D,CG+|Real.log aG|/2,hD,?_⟩
  intro B rootB phi j L hL hj hlog hCh eta heta coeff low mid high err heq hlzero hlbound hmid hhzero hhbound herr
  obtain ⟨hsl,hl⟩ := low_particle_series_bound ha hDlow j L low hlzero hlbound
  obtain ⟨hsm,hsmnorm,hmsum,hmnormsum⟩ := particleMiddleModel_sum B rootB phi hp j
  have hsnmid : Summable (fun N=>‖mid N‖) := Summable.of_nonneg_of_le (fun _=>norm_nonneg _) hmid (hsmnorm.mul_left (eta j))
  have hsmid := hsnmid.of_norm
  have hmidbound : ‖∑'N,mid N‖≤eta j*(∑i∈resonantMiddleIndices p j,‖physicalModel B rootB phi (resonantParticle p i) j‖) := by
    apply (norm_tsum_le_tsum_norm hsnmid).trans
    have hh := hsnmid.tsum_le_tsum hmid (hsmnorm.mul_left (eta j))
    simpa only [tsum_mul_left,hmnormsum] using hh
  obtain ⟨hsh0,hh0⟩ := high_range_summable_bound (j : ℝ) Chigh hj hlog hCh high hhbound
  have heqh : highRangePart (j : ℝ) high=high := by
    funext N
    by_cases hN : 1≤N ∧ (j : ℝ)/Real.sqrt (Real.log j)≤(N : ℝ)^2
    · exact ite_eq_left hN
    · simp only [highRangePart,ite_eq_right hN,hhzero N hN]
  rw [heqh] at hsh0 hh0
  have hhigh : ‖∑'N,high N‖≤DH*Real.exp ((j : ℝ)*Real.log j-j*Real.sqrt (Real.log j)/32) := by
    have hn := norm_tsum_le_tsum_norm hsh0.norm
    apply hn.trans
    simpa only [DH,div_eq_mul_inv,mul_comm,one_mul] using hh0
  obtain ⟨hse,hge⟩ := hgauss j
  have hsne : Summable (fun N=>‖err N‖) := Summable.of_nonneg_of_le (fun _=>norm_nonneg _) herr hse
  have hserr := hsne.of_norm
  have herrbound := (norm_tsum_le_tsum_norm hsne).trans ((hsne.tsum_le_tsum herr hse).trans hge)
  have hsall : Summable coeff := by
    have hs := (((hsl.add hsm).add hsmid).add hsh0).add hserr
    exact hs.congr (fun N=>(heq N).symm)
  refine ⟨hsall,L,∑'N,low N,∑'N,mid N,∑'N,high N,∑'N,err N,hL,?_,?_,hmidbound,?_,?_⟩
  · calc
      (∑'N,coeff N) = ∑'N,(low N+particleMiddleModel B rootB phi p j N+mid N+high N+err N) := tsum_congr heq
      _ = _ := by rw [(((hsl.add hsm).add hsmid).add hsh0).tsum_add hserr,
        ((hsl.add hsm).add hsmid).tsum_add hsh0,(hsl.add hsm).tsum_add hsmid,hsl.tsum_add hsm,hmsum]
  · apply hl.trans
    gcongr
  · exact hhigh.trans (mul_le_mul_of_nonneg_right hDh (Real.exp_pos _).le)
  · exact herrbound.trans (mul_le_mul_of_nonneg_right hDg (Real.exp_pos _).le)


theorem compact_family_particle_estimates_ranges (B rootB : E→ℂ→ℂ) (phi : ℝ) (Q : Set E)
    {p : ℕ} (hp : 0<p) (hpOdd : Odd p)
    {a Dlow aG : ℝ} (ha : 0<a) (hDlow : 0≤Dlow) (haG : 0<aG) (CG Chigh : ℝ)
    (coeff : E→ℕ→ℕ→ℂ) (error : ℕ→ℝ) (herror : ∀ᶠj : ℕ in atTop,0≤error j)
    (heven : ∀ eta ∈ Q, ∀j N,¬Odd N → coeff eta j N=0)
    (hlow : ∀ eta ∈ Q, ∀j N,Odd N → ‖coeff eta j N‖≤Dlow*(N : ℝ)^2*((N : ℝ)^3/a)^j)
    (hnonres : ∀ eta ∈ Q, ∀j N,Odd N → ¬p∣N →
      ‖coeff eta j N‖≤Real.exp (-aG*(N : ℝ)^2+((j : ℝ)+1)*Real.log N+CG*((j : ℝ)+1)))
    (hmiddle : ∀ᶠj : ℕ in atTop,∀ eta ∈ Q, ∀N,
      N∈(resonantMiddleIndices p j).image (resonantParticle p) →
      ‖coeff eta j N-particleMiddleModel (B eta) (rootB eta) phi p j N‖≤
        error j*‖particleMiddleModel (B eta) (rootB eta) phi p j N‖+
        Real.exp (-aG*(N : ℝ)^2+((j : ℝ)+1)*Real.log N+CG*((j : ℝ)+1)))
    (hhigh : ∀ᶠj : ℕ in atTop,∀ eta ∈ Q, ∀N : ℕ,Odd N → p∣N → Real.log j<(N : ℝ) →
      (j : ℝ)/Real.sqrt (Real.log j)<(N : ℝ)^2 →
      ‖coeff eta j N‖≤Real.exp (2*j*Real.log N-(N : ℝ)^2/2*Real.log N+Chigh*(N : ℝ)^2)+
        Real.exp (-aG*(N : ℝ)^2+((j : ℝ)+1)*Real.log N+CG*((j : ℝ)+1))) :
    ∃D C : ℝ,0<D ∧ ∀ᶠj : ℕ in atTop,
      ∀ eta ∈ Q, Summable (coeff eta j) ∧ HasCoefficientRanges (fun j=>∑'N,coeff eta j N) (B eta) (rootB eta) phi p a D C error j := by
  obtain ⟨D,C,hD,hassemble⟩ := family_particle_series_ranges hp ha hDlow haG CG Chigh
  refine ⟨D,C,hD,?_⟩
  have ht : Tendsto (fun j : ℕ=>Real.log (j : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [herror,hmiddle,hhigh,ht.eventually (eventually_ge_atTop (max 1024 (32*Chigh))),eventually_ge_atTop (1 : ℕ)]
    with j hη hm hh hlogs hj
  intro eta heta
  have hlog : 1024≤Real.log (j : ℝ) := (le_max_left _ _).trans hlogs
  have hCh : 32*Chigh≤Real.log (j : ℝ) := (le_max_right _ _).trans hlogs
  have hlog0 : 0≤Real.log (j : ℝ) := by linarith
  have hsqrt : 1≤Real.sqrt (Real.log (j : ℝ)) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (show (1 : ℝ)≤Real.log j by linarith)
  obtain ⟨low,mid,high,err,heq,hlzero,hlbound,hmbound,hhzero,hhbound,hebound⟩ :=
    pointwise_particle_partition (B eta) (rootB eta) phi hp hpOdd hlog0 hsqrt (error j) hη (coeff eta j)
      (fun N=>Dlow*(N : ℝ)^2*((N : ℝ)^3/a)^j)
      (fun N=>Real.exp (2*j*Real.log N-(N : ℝ)^2/2*Real.log N+Chigh*(N : ℝ)^2))
      (fun N=>Real.exp (-aG*(N : ℝ)^2+((j : ℝ)+1)*Real.log N+CG*((j : ℝ)+1)))
      (by intro N; positivity) (fun _=>(Real.exp_pos _).le) (fun _=>(Real.exp_pos _).le)
      (heven eta heta j) (hlow eta heta j) (hm eta heta) (hh eta heta) (hnonres eta heta j)
  have hout := hassemble (B eta) (rootB eta) phi j ⌊Real.log (j : ℝ)⌋₊ (Nat.floor_le hlog0)
    (by exact_mod_cast (show 0<j by omega)) hlog hCh error hη (coeff eta j) low mid high err heq hlzero
    (fun N _=>hlbound N) hmbound hhzero (fun N _ _=>hhbound N) hebound
  exact hout


theorem compact_family_negative_paper_ranges_of_particle_estimates
    (curve : E→ℂ→Coupling) (amp B rootB : E→ℂ→ℂ) (phi : ℝ) (Q : Set E)
    {p : ℕ} (hp : 0<p) (hpOdd : Odd p)
    {a Dlow aP aR : ℝ} (ha : 0<a) (hDlow : 0≤Dlow) (haP : 0<aP) (haR : 0<aR)
    (CP CR Chigh : ℝ) (error : ℕ→ℝ) (herror : ∀ᶠj : ℕ in atTop,0≤error j)
    (hlow : ∀ eta ∈ Q, ∀j m,‖negativePaperParticleCoefficient (curve eta) (amp eta) m j‖≤
      Dlow*((2*m+1 : ℕ) : ℝ)^2*(((2*m+1 : ℕ) : ℝ)^3/a)^j)
    (hnonres : ∀ eta ∈ Q, ∀j m,¬p∣2*m+1 → ‖negativePaperParticleCoefficient (curve eta) (amp eta) m j‖≤gaussianEnvelope aR CR (2*m+1) j)
    (hmiddle : ∀ᶠj : ℕ in atTop,∀ eta ∈ Q, ∀m,p∣2*m+1 →
      Real.log j<((2*m+1 : ℕ) : ℝ) → ((2*m+1 : ℕ) : ℝ)^2≤j/Real.sqrt (Real.log j) →
      ‖negativePaperParticleCoefficient (curve eta) (amp eta) m j-physicalModel (B eta) (rootB eta) phi (2*m+1) j‖≤
        error j*‖physicalModel (B eta) (rootB eta) phi (2*m+1) j‖+gaussianEnvelope aP CP (2*m+1) j)
    (hhigh : ∀ᶠj : ℕ in atTop,∀ eta ∈ Q, ∀m,p∣2*m+1 →
      Real.log j<((2*m+1 : ℕ) : ℝ) → (j : ℝ)/Real.sqrt (Real.log j)<((2*m+1 : ℕ) : ℝ)^2 →
      ‖negativePaperParticleCoefficient (curve eta) (amp eta) m j‖≤
        Real.exp (2*j*Real.log (2*m+1)-((2*m+1 : ℕ) : ℝ)^2/2*Real.log (2*m+1)+Chigh*((2*m+1 : ℕ) : ℝ)^2)+
        gaussianEnvelope aP CP (2*m+1) j) :
    ∃D C : ℝ,0<D ∧ ∀ᶠj : ℕ in atTop,
      ∀ eta ∈ Q, HasCoefficientRanges (negativePaperCoefficient (curve eta) (amp eta)) (B eta) (rootB eta) phi p a D C error j := by
  classical
  let coeff := fun eta j=>oddCoefficientLift (fun m=>negativePaperParticleCoefficient (curve eta) (amp eta) m j)
  let ag := min aP aR
  let cg := max CP CR
  have hag : 0<ag := lt_min haP haR
  have hleft (N j : ℕ) := gaussianEnvelope_mono (min_le_left aP aR) (le_max_left CP CR) N j
  have hright (N j : ℕ) := gaussianEnvelope_mono (min_le_right aP aR) (le_max_right CP CR) N j
  have heven : ∀ eta ∈ Q, ∀j N,¬Odd N → coeff eta j N=0 := by
    intro eta _heta j N hn
    exact ite_eq_right hn
  have hlo : ∀ eta ∈ Q, ∀j N,Odd N → ‖coeff eta j N‖≤Dlow*(N : ℝ)^2*((N : ℝ)^3/a)^j := by
    intro eta heta j N hn
    obtain ⟨m,rfl⟩ := hn
    simpa only [coeff,oddCoefficientLift_odd] using hlow eta heta j m
  have hnr : ∀ eta ∈ Q, ∀j N,Odd N → ¬p∣N → ‖coeff eta j N‖≤gaussianEnvelope ag cg N j := by
    intro eta heta j N hn hnd
    obtain ⟨m,rfl⟩ := hn
    simpa only [coeff,oddCoefficientLift_odd] using (hnonres eta heta j m hnd).trans (hright (2*m+1) j)
  have hm : ∀ᶠj : ℕ in atTop,∀ eta ∈ Q, ∀N,N∈(resonantMiddleIndices p j).image (resonantParticle p) →
      ‖coeff eta j N-particleMiddleModel (B eta) (rootB eta) phi p j N‖≤
        error j*‖particleMiddleModel (B eta) (rootB eta) phi p j N‖+gaussianEnvelope ag cg N j := by
    filter_upwards [hmiddle] with j hj
    intro eta heta N hN
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hN
    have ho : Odd (resonantParticle p i) := hpOdd.mul ⟨i,rfl⟩
    obtain ⟨m,hm⟩ := ho
    have hd : p∣2*m+1 := by rw [←hm]; exact dvd_mul_right p _
    have hcut := (Finset.mem_filter.mp hi).2
    rw [hm] at hcut
    have hh := (hj eta heta m hd hcut.1 hcut.2).trans
      (add_le_add (le_refl _) (hleft (2*m+1) j))
    rw [particleMiddleModel_at (B eta) (rootB eta) phi hp,ite_eq_left hi,hm]
    simpa only [coeff,oddCoefficientLift_odd] using hh
  have hh : ∀ᶠj : ℕ in atTop,∀ eta ∈ Q, ∀N : ℕ,Odd N → p∣N → Real.log j<(N : ℝ) →
      (j : ℝ)/Real.sqrt (Real.log j)<(N : ℝ)^2 →
      ‖coeff eta j N‖≤Real.exp (2*j*Real.log N-(N : ℝ)^2/2*Real.log N+Chigh*(N : ℝ)^2)+gaussianEnvelope ag cg N j := by
    filter_upwards [hhigh] with j hj
    intro eta heta N hn hd hlo hhi
    obtain ⟨m,rfl⟩ := hn
    have h := (hj eta heta m hd hlo hhi).trans (add_le_add (le_refl _) (hleft (2*m+1) j))
    simpa only [coeff,oddCoefficientLift_odd,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using h
  obtain ⟨D,C,hD,hout⟩ := compact_family_particle_estimates_ranges B rootB phi Q hp hpOdd ha hDlow hag cg Chigh coeff error herror heven hlo hnr hm hh
  refine ⟨D,C,hD,?_⟩
  filter_upwards [hout] with j hj
  intro eta heta
  have hj := hj eta heta
  have hf : Summable (fun m=>negativePaperParticleCoefficient (curve eta) (amp eta) m j) := by
    have hi : Function.Injective (fun m : ℕ=>2*m+1) := by intro x y h; dsimp only at h; omega
    simpa only [coeff,Function.comp_def,oddCoefficientLift_odd] using hj.1.comp_injective hi
  have he := negativePaperCoefficient_eq_oddLift hf
  change HasCoefficientRanges _ _ _ _ _ _ _ _ _ _
  unfold HasCoefficientRanges at hj ⊢
  simpa only [he,coeff] using hj.2


end
end IsingBulk.Joint.Negative
