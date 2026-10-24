import IsingBulk.Anisotropic.NegativeDominance.ParticleModelEmbedding
import IsingBulk.Anisotropic.NegativeDominance.LowParticleSeries
import IsingBulk.Anisotropic.NegativeDominance.GaussianMoment

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open scoped BigOperators

/-- Full infinite particle-series assembly. Every sum and every norm bound is
proved from pointwise actual range/error envelopes; no finite surrogate or
complete-coefficient comparison is supplied as a hypothesis. -/
theorem particle_series_ranges (B rootB : ℂ→ℂ) (phi : ℝ) {p : ℕ} (hp : 0<p)
    {a Dlow aG : ℝ} (ha : 0<a) (hDlow : 0≤Dlow) (haG : 0<aG) (CG Chigh : ℝ) :
    ∃D C : ℝ,0<D ∧ ∀j L : ℕ,(L : ℝ)≤Real.log j → (0 : ℝ)<j →
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
  intro j L hL hj hlog hCh eta heta coeff low mid high err heq hlzero hlbound hmid hhzero hhbound herr
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

end
end IsingBulk.Anisotropic.NegativeDominance
