import IsingBulk.Algebra.PrimeTheorem
import IsingBulk.HT.First.NegativeTrace

/-! F001 §3: arithmetic valid on both upper quadrants, not only the
positive-cosine range of the earlier selected-family interfaces. -/
namespace IsingBulk.HT22.Arithmetic
noncomputable section
open Polynomial IntermediateField IsingBulk.PrimeFamily

private theorem two_coprime_prime {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    Nat.Coprime 2 p := by
  exact (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))).symm

/-- A primitive prime-root trace is irrational also when its real value is negative.
The proof uses its first two normalized moments and never assumes positivity. -/
theorem primitive_trace_not_rational {L : Type*} [Field L] [Algebra ℚ L]
    [Algebra.IsIntegral ℚ L] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {r : L} (hr : IsPrimitiveRoot r p) (q : ℚ) :
    r + r⁻¹ ≠ algebraMap ℚ L q := by
  intro hq
  have hr0 : r ≠ 0 := hr.ne_zero (by omega)
  have hr2 := hr.pow_of_coprime 2 (two_coprime_prime hp hp5)
  have hri2 := hr.inv.pow_of_coprime 2 (two_coprime_prime hp hp5)
  have ht := congrArg (Algebra.normalizedTrace ℚ L) hq
  simp only [map_add, normalizedTrace_primitive_root hp hr,
    normalizedTrace_primitive_root hp hr.inv,
    Algebra.normalizedTrace_algebraMap_apply ℚ ℚ L,
    Algebra.normalizedTrace_self_apply] at ht
  have hs : r^2 + (r⁻¹)^2 = algebraMap ℚ L (q^2-2) := by
    have hh : (r+r⁻¹)^2 = r^2+(r⁻¹)^2+2 := by field_simp; ring
    rw [hq] at hh
    norm_num only [map_sub, map_pow, map_ofNat]
    linear_combination -hh
  have ht2 := congrArg (Algebra.normalizedTrace ℚ L) hs
  simp only [map_add, normalizedTrace_primitive_root hp hr2,
    normalizedTrace_primitive_root hp hri2,
    Algebra.normalizedTrace_algebraMap_apply ℚ ℚ L,
    Algebra.normalizedTrace_self_apply] at ht2
  have hnpos : (0 : ℚ) < ((p-1 : ℕ) : ℚ) := by exact_mod_cast (show 0 < p-1 by omega)
  have hd : (0 : ℚ) < ((p-1 : ℕ) : ℚ)⁻¹ := inv_pos.mpr hnpos
  have hdlt : ((p-1 : ℕ) : ℚ)⁻¹ < 1/2 := by
    have hn : (2 : ℚ) < ((p-1 : ℕ) : ℚ) := by exact_mod_cast (show 2 < p-1 by omega)
    have hm := inv_mul_cancel₀ hnpos.ne'
    nlinarith [mul_lt_mul_of_pos_left hn hd]
  have he : (q-2)*(q+1)=0 := by nlinarith [ht,ht2]
  rcases mul_eq_zero.mp he with he | he <;> linarith

/-- Both signs of the physical endpoint are nonresonant. The second moment
obstruction replaces any unproved extension-of-embeddings premise. -/
theorem signed_branch_trace_obstruction {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {r z : AlgebraicComplex} (hr : IsPrimitiveRoot r p)
    (hz0 : z ≠ 0) {ε : ℚ} (hε : ε=1 ∨ ε= -1)
    (hrel : z+z⁻¹ = (2*ε) • (r+r⁻¹)-2) : ¬ IsOfFinOrder z := by
  have hr0 : r ≠ 0 := hr.ne_zero hp.ne_zero
  have hr2 := hr.pow_of_coprime 2 (two_coprime_prime hp hp5)
  have hri2 := hr.inv.pow_of_coprime 2 (two_coprime_prime hp hp5)
  have hzcalc : (z+z⁻¹)^2=z^2+(z⁻¹)^2+2 := by field_simp; ring
  have hrcalc : (r+r⁻¹)^2=r^2+(r⁻¹)^2+2 := by field_simp; ring
  have hsq := congrArg (fun w : AlgebraicComplex => w^2) hrel
  have hh : z^2+(z⁻¹)^2 = (4:ℚ) • r^2 + (4:ℚ) • (r⁻¹)^2 -
      (8*ε) • (r+r⁻¹)+10 := by
    rcases hε with hε | hε <;> subst ε
    all_goals norm_num [Algebra.smul_def] at hsq ⊢
    all_goals linear_combination hsq - hzcalc + 4*hrcalc
  have ht := congrArg (Algebra.normalizedTrace ℚ AlgebraicComplex) hh
  have ht10 : Algebra.normalizedTrace ℚ AlgebraicComplex 10=10 := by
    simpa using Algebra.normalizedTrace_algebraMap_apply ℚ ℚ AlgebraicComplex 10
  simp only [map_add, map_sub, map_smul, normalizedTrace_primitive_root hp hr,
    normalizedTrace_primitive_root hp hr.inv, normalizedTrace_primitive_root hp hr2,
    normalizedTrace_primitive_root hp hri2, ht10, smul_eq_mul] at ht
  intro hz
  obtain ⟨N,hN,hzN⟩ := isOfFinOrder_iff_pow_eq_one.mp hz
  have hz2N : (z^2)^N=1 := by
    rw [← pow_mul, Nat.mul_comm 2 N, pow_mul, hzN, one_pow]
  have hzi2N : ((z⁻¹)^2)^N=1 := by simp only [inv_pow, hz2N, inv_one]
  have hupper := IsingBulk.HT.First.normalizedTrace_root_unity_upper (z^2) hN hz2N
  have hiupper := IsingBulk.HT.First.normalizedTrace_root_unity_upper ((z⁻¹)^2) hN hzi2N
  have hnpos : (0:ℚ)<((p-1:ℕ):ℚ) := by exact_mod_cast (show 0<p-1 by omega)
  have hd := inv_pos.mpr hnpos
  have hdinv := inv_mul_cancel₀ hnpos.ne'
  have hn : (4:ℚ)≤((p-1:ℕ):ℚ) := by exact_mod_cast (show 4≤p-1 by omega)
  have hdle : ((p-1:ℕ):ℚ)⁻¹≤1/4 := by
    nlinarith [mul_le_mul_of_nonneg_left hn hd.le]
  rcases hε with hε | hε <;> rw [hε] at ht <;> nlinarith

end
end IsingBulk.HT22.Arithmetic
