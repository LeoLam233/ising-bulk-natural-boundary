import IsingBulk.Anisotropic.NegativeDominance.ParticleModelEmbedding
import IsingBulk.Anisotropic.NegativeDominance.ComplexErrorSplit

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open scoped BigOperators

theorem pointwise_particle_partition (B rootB : ℂ→ℂ) (phi : ℝ)
    {p j : ℕ} (hp : 0<p) (hpOdd : Odd p) (hlog : 0≤Real.log (j : ℝ))
    (hsqrt : 1≤Real.sqrt (Real.log j)) (eta : ℝ) (heta : 0≤eta)
    (coeff : ℕ→ℂ) (Low High G : ℕ→ℝ)
    (hLow : ∀N,0≤Low N) (hHigh : ∀N,0≤High N) (hG : ∀N,0≤G N)
    (heven : ∀N,¬Odd N → coeff N=0)
    (hlow : ∀N,Odd N → ‖coeff N‖≤Low N)
    (hmiddle : ∀N,N∈(resonantMiddleIndices p j).image (resonantParticle p) →
      ‖coeff N-particleMiddleModel B rootB phi p j N‖≤eta*‖particleMiddleModel B rootB phi p j N‖+G N)
    (hhigh : ∀N : ℕ,Odd N → p∣N → Real.log j<(N : ℝ) →
      (j : ℝ)/Real.sqrt (Real.log j)<(N : ℝ)^2 → ‖coeff N‖≤High N+G N)
    (hnonres : ∀N,Odd N → ¬p∣N → ‖coeff N‖≤G N) :
    ∃low mid high err : ℕ→ℂ,
      (∀N,coeff N=low N+particleMiddleModel B rootB phi p j N+mid N+high N+err N) ∧
      (∀N,⌊Real.log (j : ℝ)⌋₊<N → low N=0) ∧
      (∀N,‖low N‖≤Low N) ∧
      (∀N,‖mid N‖≤eta*‖particleMiddleModel B rootB phi p j N‖) ∧
      (∀N : ℕ,¬(1≤N ∧ (j : ℝ)/Real.sqrt (Real.log j)≤(N : ℝ)^2) → high N=0) ∧
      (∀N,‖high N‖≤High N) ∧ (∀N,‖err N‖≤G N) := by
  classical
  have hex : ∀N : ℕ,∃l m h e : ℂ,
      coeff N=l+particleMiddleModel B rootB phi p j N+m+h+e ∧
      (⌊Real.log (j : ℝ)⌋₊<N → l=0) ∧ ‖l‖≤Low N ∧
      ‖m‖≤eta*‖particleMiddleModel B rootB phi p j N‖ ∧
      (¬(1≤N ∧ (j : ℝ)/Real.sqrt (Real.log j)≤(N : ℝ)^2) → h=0) ∧
      ‖h‖≤High N ∧ ‖e‖≤G N := by
    intro N
    have hm0 : 0≤eta*‖particleMiddleModel B rootB phi p j N‖ := mul_nonneg heta (norm_nonneg _)
    by_cases ho : Odd N
    · by_cases hl : N≤⌊Real.log (j : ℝ)⌋₊
      · have hn : N∉(resonantMiddleIndices p j).image (resonantParticle p) := by
          intro hi
          have hi' := (resonantMiddle_image_iff hp hpOdd hsqrt N).mp hi
          have hfloor : (N : ℝ)≤⌊Real.log (j : ℝ)⌋₊ := by exact_mod_cast hl
          have hle : (N : ℝ)≤Real.log j := hfloor.trans (Nat.floor_le hlog)
          exact (not_lt_of_ge hle) hi'.2.2.1
        have hmz := particleMiddleModel_zero_of_not_image B rootB phi hp j N hn
        refine ⟨coeff N,0,0,0,by simp only [hmz,add_zero],?_,hlow N ho,?_,fun _=>rfl,?_,?_⟩
        · intro h; omega
        · simpa only [norm_zero] using hm0
        · simpa only [norm_zero] using hHigh N
        · simpa only [norm_zero] using hG N
      have hlarge : Real.log j<(N : ℝ) := (Nat.floor_lt hlog).mp (Nat.lt_of_not_ge hl)
      by_cases hd : p∣N
      · by_cases hcut : (N : ℝ)^2≤j/Real.sqrt (Real.log j)
        · have hi := (resonantMiddle_image_iff hp hpOdd hsqrt N).mpr ⟨ho,hd,hlarge,hcut⟩
          obtain ⟨u,v,huv,hu,hv⟩ := complex_error_split hm0 (hG N) (hmiddle N hi)
          refine ⟨0,u,0,v,?_,fun _=>rfl,?_,hu,fun _=>rfl,?_,hv⟩
          · linear_combination huv
          · simpa only [norm_zero] using hLow N
          · simpa only [norm_zero] using hHigh N
        · have hc := lt_of_not_ge hcut
          have hn : N∉(resonantMiddleIndices p j).image (resonantParticle p) := by
            intro hi; exact hcut ((resonantMiddle_image_iff hp hpOdd hsqrt N).mp hi).2.2.2
          have hmz := particleMiddleModel_zero_of_not_image B rootB phi hp j N hn
          obtain ⟨u,v,huv,hu,hv⟩ := complex_error_split (hHigh N) (hG N) (hhigh N ho hd hlarge hc)
          refine ⟨0,0,u,v,by simpa only [hmz,zero_add,add_zero] using huv,fun _=>rfl,?_,?_,?_,hu,hv⟩
          · simpa only [norm_zero] using hLow N
          · simpa only [norm_zero] using hm0
          · intro hh; exact (hh ⟨ho.pos,hc.le⟩).elim
      · have hn : N∉(resonantMiddleIndices p j).image (resonantParticle p) := by
          intro hi; exact hd ((resonantMiddle_image_iff hp hpOdd hsqrt N).mp hi).2.1
        have hmz := particleMiddleModel_zero_of_not_image B rootB phi hp j N hn
        refine ⟨0,0,0,coeff N,by simp only [hmz,zero_add],fun _=>rfl,?_,?_,fun _=>rfl,?_,hnonres N ho hd⟩
        · simpa only [norm_zero] using hLow N
        · simpa only [norm_zero] using hm0
        · simpa only [norm_zero] using hHigh N
    · have hn : N∉(resonantMiddleIndices p j).image (resonantParticle p) := by
        intro hi; exact ho ((resonantMiddle_image_iff hp hpOdd hsqrt N).mp hi).1
      have hmz := particleMiddleModel_zero_of_not_image B rootB phi hp j N hn
      refine ⟨0,0,0,0,by simp only [heven N ho,hmz,add_zero],fun _=>rfl,?_,?_,fun _=>rfl,?_,?_⟩
      · simpa only [norm_zero] using hLow N
      · simpa only [norm_zero] using hm0
      · simpa only [norm_zero] using hHigh N
      · simpa only [norm_zero] using hG N
  choose low mid high err heq hlzero hlbound hmbound hhzero hhbound hebound using hex
  exact ⟨low,mid,high,err,heq,hlzero,hlbound,hmbound,hhzero,hhbound,hebound⟩

end
end IsingBulk.Anisotropic.NegativeDominance
