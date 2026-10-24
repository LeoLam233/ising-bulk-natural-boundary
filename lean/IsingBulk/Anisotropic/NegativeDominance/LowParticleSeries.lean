import IsingBulk.Anisotropic.NegativeDominance.CoefficientRanges

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open scoped BigOperators

/-- Exact finite support of the growing low particle range, not a fixed
finite family. The index zero contributes zero through the quadratic bound. -/
theorem low_particle_series_bound {a D : ℝ} (ha : 0<a) (hD : 0≤D)
    (j L : ℕ) (f : ℕ→ℂ) (hzero : ∀N : ℕ,L<N → f N=0)
    (hbound : ∀N : ℕ,N≤L → ‖f N‖≤D*(N : ℝ)^2*((N : ℝ)^3/a)^j) :
    Summable f ∧ ‖∑'N,f N‖≤D*(L : ℝ)^3*((L : ℝ)^3/a)^j := by
  have hsupport : ∀N : ℕ,N∉Finset.range (L+1) → f N=0 := by
    intro N hN
    exact hzero N (by simp only [Finset.mem_range] at hN; omega)
  have hs : Summable f := summable_of_ne_finset_zero hsupport
  have h0 : f 0=0 := by
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    simpa only [Nat.cast_zero,zero_pow (by norm_num : 2≠0),mul_zero,zero_mul] using hbound 0 (Nat.zero_le L)
  refine ⟨hs,?_⟩
  rw [tsum_eq_sum hsupport,Finset.sum_range_succ']
  rw [h0,add_zero]
  calc
    _ ≤ ∑n∈Finset.range L,‖f (n+1)‖ := norm_sum_le _ _
    _ ≤ ∑_n∈Finset.range L,D*(L : ℝ)^2*((L : ℝ)^3/a)^j := by
      apply Finset.sum_le_sum
      intro n hn
      have hnL : n+1≤L := Finset.mem_range.mp hn
      apply (hbound (n+1) hnL).trans
      have hle : ((n+1 : ℕ) : ℝ)≤L := by exact_mod_cast hnL
      gcongr
    _ = D*(L : ℝ)^3*((L : ℝ)^3/a)^j := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; ring

end
end IsingBulk.Anisotropic.NegativeDominance
