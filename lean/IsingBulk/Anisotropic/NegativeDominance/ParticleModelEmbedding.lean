import IsingBulk.Anisotropic.NegativeDominance.CoefficientRanges

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open scoped BigOperators

/-- Embed the finite complete resonant middle model in the full particle index. -/
def particleMiddleModel (B rootB : ℂ→ℂ) (phi : ℝ) (p j : ℕ) : ℕ→ℂ :=
  Function.extend (resonantParticle p)
    (fun i=>if i∈resonantMiddleIndices p j then physicalModel B rootB phi (resonantParticle p i) j else 0) 0

theorem norm_extend_zero {f : ℕ→ℕ} (hf : Function.Injective f) (g : ℕ→ℂ) :
    (fun N=>‖Function.extend f g 0 N‖)=Function.extend f (fun i=>‖g i‖) 0 := by
  funext N
  by_cases h : ∃i,f i=N
  · obtain ⟨i,rfl⟩ := h
    rw [hf.extend_apply,hf.extend_apply]
  · rw [Function.extend_apply' _ _ _ h,Function.extend_apply' _ _ _ h]
    simp only [Pi.zero_apply,norm_zero]

theorem particleMiddleModel_at (B rootB : ℂ→ℂ) (phi : ℝ) {p : ℕ} (hp : 0<p) (j i : ℕ) :
    particleMiddleModel B rootB phi p j (resonantParticle p i)=
      if i∈resonantMiddleIndices p j then physicalModel B rootB phi (resonantParticle p i) j else 0 :=
  (resonantParticle_injective hp).extend_apply _ _ _

theorem particleMiddleModel_sum (B rootB : ℂ→ℂ) (phi : ℝ) {p : ℕ} (hp : 0<p) (j : ℕ) :
    Summable (particleMiddleModel B rootB phi p j) ∧
    Summable (fun N=>‖particleMiddleModel B rootB phi p j N‖) ∧
    (∑'N,particleMiddleModel B rootB phi p j N)=
      ∑i∈resonantMiddleIndices p j,physicalModel B rootB phi (resonantParticle p i) j ∧
    (∑'N,‖particleMiddleModel B rootB phi p j N‖)=
      ∑i∈resonantMiddleIndices p j,‖physicalModel B rootB phi (resonantParticle p i) j‖ := by
  classical
  let g := fun i=>if i∈resonantMiddleIndices p j then physicalModel B rootB phi (resonantParticle p i) j else 0
  have hs : Summable g := summable_of_ne_finset_zero (s := resonantMiddleIndices p j) (by intro i hi; simp only [g,ite_eq_right hi])
  have hsn : Summable (fun i=>‖g i‖) := summable_of_ne_finset_zero (s := resonantMiddleIndices p j) (by intro i hi; simp only [g,ite_eq_right hi,norm_zero])
  have hn : (fun N=>‖particleMiddleModel B rootB phi p j N‖)=Function.extend (resonantParticle p) (fun i=>‖g i‖) 0 := norm_extend_zero (resonantParticle_injective hp) g
  refine ⟨(summable_extend_zero (resonantParticle_injective hp)).mpr hs,?_,?_,?_⟩
  · rw [hn]; exact (summable_extend_zero (resonantParticle_injective hp)).mpr hsn
  · rw [particleMiddleModel,tsum_extend_zero (resonantParticle_injective hp)]
    rw [tsum_eq_sum (s := resonantMiddleIndices p j) (by intro i hi; exact ite_eq_right hi)]
    apply Finset.sum_congr rfl
    intro i hi
    exact ite_eq_left hi
  · rw [hn,tsum_extend_zero (resonantParticle_injective hp)]
    rw [tsum_eq_sum (s := resonantMiddleIndices p j) (by intro i hi; simp only [g,ite_eq_right hi,norm_zero])]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [g,ite_eq_left hi]


theorem particleMiddleModel_zero_of_not_image (B rootB : ℂ→ℂ) (phi : ℝ)
    {p : ℕ} (hp : 0<p) (j N : ℕ)
    (hN : N∉(resonantMiddleIndices p j).image (resonantParticle p)) :
    particleMiddleModel B rootB phi p j N=0 := by
  classical
  by_cases h : ∃i,resonantParticle p i=N
  · obtain ⟨i,rfl⟩ := h
    rw [particleMiddleModel_at B rootB phi hp]
    apply ite_eq_right
    intro hi
    exact hN (Finset.mem_image.mpr ⟨i,hi,rfl⟩)
  · exact Function.extend_apply' _ _ _ h

theorem resonantMiddle_image_iff {p j : ℕ} (hp : 0<p) (hpOdd : Odd p)
    (hs : 1≤Real.sqrt (Real.log j)) (N : ℕ) :
    N∈(resonantMiddleIndices p j).image (resonantParticle p) ↔
      Odd N ∧ p∣N ∧ Real.log j<(N : ℝ) ∧ (N : ℝ)^2≤j/Real.sqrt (Real.log j) := by
  classical
  constructor
  · intro hN
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hN
    refine ⟨hpOdd.mul ⟨i,rfl⟩,?_,(middle_index_mem_iff hp hs i).mp hi⟩
    exact dvd_mul_right p (2*i+1)
  · rintro ⟨hOdd,hdiv,hlo,hhi⟩
    obtain ⟨i,rfl⟩ := (odd_dvd_resonant_iff hpOdd).mp ⟨hOdd,hdiv⟩
    exact Finset.mem_image.mpr ⟨i,(middle_index_mem_iff hp hs i).mpr ⟨hlo,hhi⟩,rfl⟩

end
end IsingBulk.Anisotropic.NegativeDominance
