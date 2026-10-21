import IsingBulk.Algebra.BranchArithmetic

/-! The second-moment trace obstruction needed on the negative-cosine half.
This extends the LT first-moment calculation, which only rules out the +1
branch on the positive family. No branch nonresonance is assumed. -/
namespace IsingBulk.HT.First
noncomputable section
open IsingBulk.PrimeFamily

/-- Any p-th root has normalized trace at least −1/(p−1); the root 1 is
allowed. This makes cross terms harmless even when primitive roots coincide. -/
theorem normalizedTrace_prime_root_lower {L : Type*} [Field L] [Algebra ℚ L]
    [Algebra.IsIntegral ℚ L] {p : ℕ} (hp : p.Prime) {z : L} (hz : z^p=1) :
    -((p-1:ℕ):ℚ)⁻¹ ≤ Algebra.normalizedTrace ℚ L z := by
  by_cases h1 : z=1
  · subst z
    have ht : Algebra.normalizedTrace ℚ L 1 = 1 := by
      simpa using Algebra.normalizedTrace_algebraMap_apply_eq_self ℚ L (1:ℚ)
    rw [ht]
    have hi : 0 ≤ ((p-1:ℕ):ℚ)⁻¹ := by positivity
    linarith
  · let : Fact p.Prime := ⟨hp⟩
    have hprim : IsPrimitiveRoot z p := IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime hz h1)
    rw [normalizedTrace_primitive_root hp hprim]

/-- Upper counterpart of the established LT root-of-unity trace lower bound. -/
theorem normalizedTrace_root_unity_upper (z : AlgebraicComplex) {N : ℕ}
    (hN : 0 < N) (hz : z^N=1) : Algebra.normalizedTrace ℚ AlgebraicComplex z ≤ 1 := by
  have hneg : (-z)^(2*N)=1 := by
    calc
      (-z)^(2*N) = ((-z)^2)^N := pow_mul _ _ _
      _ = (z^2)^N := by rw [neg_sq]
      _ = (z^N)^2 := by rw [← pow_mul,mul_comm 2 N,pow_mul]
      _ = 1 := by rw [hz,one_pow]
  have ht := normalizedTrace_root_unity_lower (-z) (by positivity : 0 < 2*N) hneg
  rw [map_neg] at ht
  linarith

/-- A root-of-unity cosine has second normalized moment at most four. -/
theorem normalizedTrace_root_cosine_square_le (z : AlgebraicComplex) {N : ℕ}
    (hN : 0 < N) (hz : z^N=1) :
    Algebra.normalizedTrace ℚ AlgebraicComplex ((z+z⁻¹)^2) ≤ 4 := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h,zero_pow hN.ne'] at hz
    exact zero_ne_one hz
  have hz2 : (z^2)^N=1 := by rw [← pow_mul,mul_comm 2 N,pow_mul,hz,one_pow]
  have hi2 : ((z⁻¹)^2)^N=1 := by simpa only [inv_pow,inv_one] using congrArg Inv.inv hz2
  have h1 := normalizedTrace_root_unity_upper (z^2) hN hz2
  have h2 := normalizedTrace_root_unity_upper ((z⁻¹)^2) hN hi2
  have ht2 : Algebra.normalizedTrace ℚ AlgebraicComplex 2 = 2 := by
    simpa using Algebra.normalizedTrace_algebraMap_apply_eq_self ℚ AlgebraicComplex (2:ℚ)
  have hsq : (z+z⁻¹)^2 = z^2+(z⁻¹)^2+2 := by field_simp; ring
  rw [hsq,map_add,map_add,ht2]
  linarith

/-- The second moment of four primitive p-roots is bounded from below without
assuming their distinctness or selecting a different complex embedding. -/
theorem normalizedTrace_primitive_sum_square_lower {L : Type*} [Field L] [Algebra ℚ L]
    [Algebra.IsIntegral ℚ L] {p : ℕ} (hp : p.Prime) {r s : L}
    (hr : IsPrimitiveRoot r p) (hs : IsPrimitiveRoot s p) :
    4-12*((p-1:ℕ):ℚ)⁻¹ ≤
      Algebra.normalizedTrace ℚ L ((r+r⁻¹+s+s⁻¹)^2) := by
  have hr0 := hr.ne_zero hp.ne_zero
  have hs0 := hs.ne_zero hp.ne_zero
  have hri : (r⁻¹)^p=1 := by simp [inv_pow,hr.pow_eq_one]
  have hsi : (s⁻¹)^p=1 := by simp [inv_pow,hs.pow_eq_one]
  have hmul (x y : L) (hx : x^p=1) (hy : y^p=1) : (x*y)^p=1 := by rw [mul_pow,hx,hy,one_mul]
  have h1 := normalizedTrace_prime_root_lower hp (hmul r r hr.pow_eq_one hr.pow_eq_one)
  have h2 := normalizedTrace_prime_root_lower hp (hmul r⁻¹ r⁻¹ hri hri)
  have h3 := normalizedTrace_prime_root_lower hp (hmul s s hs.pow_eq_one hs.pow_eq_one)
  have h4 := normalizedTrace_prime_root_lower hp (hmul s⁻¹ s⁻¹ hsi hsi)
  have h5 := normalizedTrace_prime_root_lower hp (hmul r s hr.pow_eq_one hs.pow_eq_one)
  have h6 := normalizedTrace_prime_root_lower hp (hmul r s⁻¹ hr.pow_eq_one hsi)
  have h7 := normalizedTrace_prime_root_lower hp (hmul r⁻¹ s hri hs.pow_eq_one)
  have h8 := normalizedTrace_prime_root_lower hp (hmul r⁻¹ s⁻¹ hri hsi)
  have ht4 : Algebra.normalizedTrace ℚ L 4 = 4 := by
    simpa using Algebra.normalizedTrace_algebraMap_apply_eq_self ℚ L (4:ℚ)
  have he : (r+r⁻¹+s+s⁻¹)^2 = r*r+r⁻¹*r⁻¹+s*s+s⁻¹*s⁻¹+
      2*(r*s+r*s⁻¹+r⁻¹*s+r⁻¹*s⁻¹)+4 := by field_simp; ring
  rw [he]
  simp only [two_mul,map_add,ht4]
  linarith

private theorem prime_inverse_bound {p : ℕ} (hp11 : 11 ≤ p) :
    0 < ((p-1:ℕ):ℚ)⁻¹ ∧ ((p-1:ℕ):ℚ)⁻¹ ≤ 1/10 := by
  have hp : (10:ℚ) ≤ (p-1:ℕ) := by exact_mod_cast (show 10 ≤ p-1 by omega)
  constructor
  · exact inv_pos.mpr (by linarith)
  · have h := one_div_le_one_div_of_le (by norm_num : (0:ℚ)<10) hp
    simpa only [one_div] using h

/-- In contrast to the LT positive-only lemma, this excludes every rational
value, including the negative first-moment candidate. -/
theorem primitive_sum_not_rational {L : Type*} [Field L] [Algebra ℚ L]
    [Algebra.IsIntegral ℚ L] {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) {r s : L}
    (hr : IsPrimitiveRoot r p) (hs : IsPrimitiveRoot s p) (q : ℚ) :
    r+r⁻¹+s+s⁻¹ ≠ algebraMap ℚ L q := by
  intro he
  have ht := congrArg (Algebra.normalizedTrace ℚ L) he
  rw [map_add,map_add,map_add,normalizedTrace_primitive_root hp hr,
    normalizedTrace_primitive_root hp hr.inv,normalizedTrace_primitive_root hp hs,
    normalizedTrace_primitive_root hp hs.inv,
    Algebra.normalizedTrace_algebraMap_apply_eq_self] at ht
  have hsq := normalizedTrace_primitive_sum_square_lower hp hr hs
  rw [he,← map_pow (algebraMap ℚ L),Algebra.normalizedTrace_algebraMap_apply_eq_self] at hsq
  obtain ⟨hpos,hsmall⟩ := prime_inverse_bound hp11
  have hmul := mul_nonneg hpos.le (sub_nonneg.mpr hsmall)
  nlinarith

/-- The negative-boundary branch has `+2`, where the LT first-moment
obstruction does not suffice. Its second moment contradicts root-of-unity
boundedness for p≥11. -/
theorem negative_branch_trace_obstruction {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    {r s z : AlgebraicComplex} (hr : IsPrimitiveRoot r p) (hs : IsPrimitiveRoot s p)
    (hrel : z+z⁻¹ = r+r⁻¹+s+s⁻¹+2) : ¬ IsOfFinOrder z := by
  intro hz
  obtain ⟨N,hN,hzN⟩ := isOfFinOrder_iff_pow_eq_one.mp hz
  have hupper := normalizedTrace_root_cosine_square_le z hN hzN
  have hlower := normalizedTrace_primitive_sum_square_lower hp hr hs
  have hsum : Algebra.normalizedTrace ℚ AlgebraicComplex (r+r⁻¹+s+s⁻¹) =
      -4*((p-1:ℕ):ℚ)⁻¹ := by
    rw [map_add,map_add,map_add,normalizedTrace_primitive_root hp hr,
      normalizedTrace_primitive_root hp hr.inv,normalizedTrace_primitive_root hp hs,
      normalizedTrace_primitive_root hp hs.inv]
    ring
  have ht4 : Algebra.normalizedTrace ℚ AlgebraicComplex 4 = 4 := by
    simpa using Algebra.normalizedTrace_algebraMap_apply_eq_self ℚ AlgebraicComplex (4:ℚ)
  have he (x : AlgebraicComplex) : (x+2)^2 = x^2+x+x+x+x+4 := by ring
  rw [hrel,he] at hupper
  simp only [map_add,hsum,ht4] at hupper
  obtain ⟨_hpos,hsmall⟩ := prime_inverse_bound hp11
  linarith

end
end IsingBulk.HT.First
