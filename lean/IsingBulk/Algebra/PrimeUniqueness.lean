import IsingBulk.Algebra.NickelOrder

/-! Exact rational-relation argument for uniqueness of the cosine pair. -/
namespace IsingBulk.PrimeFamily
noncomputable section
open Polynomial IntermediateField
open scoped IntermediateField

/-- A relation supported on the nonconstant powers below p must vanish identically. -/
theorem prime_polynomial_zero {L : Type*} [Field L] [Algebra ℚ L]
    {p : ℕ} (hp : p.Prime) {ζ : L} (hζ : IsPrimitiveRoot ζ p)
    {P : ℚ[X]} (hdeg : P.natDegree ≤ p - 1) (hzero : P.coeff 0 = 0)
    (hroot : aeval ζ P = 0) : P = 0 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hm := hζ.minpoly_eq_cyclotomic_of_irreducible (cyclotomic.irreducible_rat hp.pos)
  have hdvd : cyclotomic p ℚ ∣ P := by rw [hm]; exact minpoly.dvd ℚ ζ hroot
  have heq := eq_mul_leadingCoeff_of_monic_of_dvd_of_natDegree_le
    (cyclotomic.monic p ℚ) hdvd (by simpa [natDegree_cyclotomic, Nat.totient_prime hp] using hdeg)
  have hc := congrArg (fun Q : ℚ[X] => Q.coeff 0) heq
  simp [hzero, cyclotomic_coeff_zero ℚ hp.one_lt] at hc
  rw [heq, ← hc, C_0, mul_zero]

theorem primitive_root_nonzero_exponent {L : Type*} [Field L]
    {p : ℕ} (hp : p.Prime) {ζ r : L} (hζ : IsPrimitiveRoot ζ p)
    (hr : IsPrimitiveRoot r p) : ∃ i : ℕ, 0 < i ∧ i < p ∧ ζ ^ i = r := by
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨i, hi, heq⟩ := hζ.eq_pow_of_pow_eq_one hr.pow_eq_one
  refine ⟨i, ?_, hi, heq⟩
  by_contra h
  have : i = 0 := by omega
  exact hr.ne_one hp.one_lt (by simpa [this] using heq.symm)

theorem primitive_trace_pair_unique {L : Type*} [Field L] [Algebra ℚ L]
    {p : ℕ} (hp : p.Prime) {x y r s : L}
    (hx : IsPrimitiveRoot x p) (hy : IsPrimitiveRoot y p)
    (hr : IsPrimitiveRoot r p) (hs : IsPrimitiveRoot s p)
    (h : r + r⁻¹ + s + s⁻¹ = x + x⁻¹ + y + y⁻¹) :
    r + r⁻¹ = x + x⁻¹ ∨ r + r⁻¹ = y + y⁻¹ := by
  obtain ⟨i, hi0, hip, hi⟩ := primitive_root_nonzero_exponent hp hx hr
  obtain ⟨j, hj0, hjp, hj⟩ := primitive_root_nonzero_exponent hp hx hr.inv
  obtain ⟨k, hk0, hkp, hk⟩ := primitive_root_nonzero_exponent hp hx hs
  obtain ⟨l, hl0, hlp, hl⟩ := primitive_root_nonzero_exponent hp hx hs.inv
  obtain ⟨u, hu0, hup, hu⟩ := primitive_root_nonzero_exponent hp hx hx
  obtain ⟨v, hv0, hvp, hv⟩ := primitive_root_nonzero_exponent hp hx hx.inv
  obtain ⟨w, hw0, hwp, hw⟩ := primitive_root_nonzero_exponent hp hx hy
  obtain ⟨z, hz0, hzp, hz⟩ := primitive_root_nonzero_exponent hp hx hy.inv
  let P : ℚ[X] := (X^i + X^j + X^k + X^l) - (X^u + X^v + X^w + X^z)
  have hdeg : P.natDegree ≤ p - 1 := by
    have hd (m : ℕ) (hm : m < p) : (X^m : ℚ[X]).natDegree ≤ p-1 := by
      rw [natDegree_X_pow]
      omega
    dsimp [P]
    exact (natDegree_sub_le _ _).trans (max_le
      (natDegree_add_le_of_degree_le
        (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le (hd i hip) (hd j hjp)) (hd k hkp)) (hd l hlp))
      (natDegree_add_le_of_degree_le
        (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le (hd u hup) (hd v hvp)) (hd w hwp)) (hd z hzp)))
  have hconst : P.coeff 0 = 0 := by
    simp [P, coeff_X_pow, hi0.ne, hj0.ne, hk0.ne, hl0.ne, hu0.ne, hv0.ne, hw0.ne, hz0.ne]
  have heval : aeval x P = 0 := by
    simp only [P, map_sub, map_add, map_pow, aeval_X, hi, hj, hk, hl, hu, hv, hw, hz]
    exact sub_eq_zero.mpr h
  have heq := prime_polynomial_zero hp hx hdeg hconst heval
  have hmem : r = x ∨ r = x⁻¹ ∨ r = y ∨ r = y⁻¹ := by
    by_contra hh
    push Not at hh
    have hiu : u ≠ i := fun he => hh.1 (hi.symm.trans (he ▸ hu))
    have hiv : v ≠ i := fun he => hh.2.1 (hi.symm.trans (he ▸ hv))
    have hiw : w ≠ i := fun he => hh.2.2.1 (hi.symm.trans (he ▸ hw))
    have hiz : z ≠ i := fun he => hh.2.2.2 (hi.symm.trans (he ▸ hz))
    have hc := congrArg (fun Q : ℚ[X] => Q.coeff i) heq
    simp [P, coeff_X_pow, Ne.symm hiu, Ne.symm hiv, Ne.symm hiw, Ne.symm hiz] at hc
    split_ifs at hc <;> norm_num at hc
  rcases hmem with hmem | hmem | hmem | hmem
  · exact Or.inl (by rw [hmem])
  · exact Or.inl (by rw [hmem, inv_inv, add_comm])
  · exact Or.inr (by rw [hmem])
  · exact Or.inr (by rw [hmem, inv_inv, add_comm])

theorem double_prime_root_cases {L : Type*} [Field L] {p : ℕ}
    (hp : p.Prime) (hp2 : 2 < p) {z : L} (hz : z ^ (2*p) = 1) :
    z = 1 ∨ z = -1 ∨ IsPrimitiveRoot z p ∨ IsPrimitiveRoot (-z) p := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hpow : (z^p)^2 = 1 := by simpa [← pow_mul, Nat.mul_comm p 2] using hz
  rcases sq_eq_one_iff.mp hpow with h | h
  · by_cases h1 : z = 1
    · exact Or.inl h1
    · exact Or.inr (Or.inr (Or.inl (isPrimitiveRoot_of_mem_nthRootsFinset hp
        ((Polynomial.mem_nthRootsFinset hp.pos 1).mpr h) h1)))
  · by_cases hm : z = -1
    · exact Or.inr (Or.inl hm)
    · have hn : (-z)^p = 1 := by rw [hodd.neg_pow, h]; simp
      exact Or.inr (Or.inr (Or.inr (isPrimitiveRoot_of_mem_nthRootsFinset hp
        ((Polynomial.mem_nthRootsFinset hp.pos 1).mpr hn) (fun hh => hm (neg_eq_iff_eq_neg.mp hh)))))

theorem double_prime_trace_cases {L : Type*} [Field L] [Algebra ℚ L]
    [Algebra.IsIntegral ℚ L] {p : ℕ} (hp : p.Prime) (hp2 : 2 < p)
    {z : L} (hz : z ^ (2*p) = 1) :
    (IsPrimitiveRoot z p ∧ Algebra.normalizedTrace ℚ L (z + z⁻¹) = -2 * ((p-1 : ℕ) : ℚ)⁻¹) ∨
    Algebra.normalizedTrace ℚ L (z + z⁻¹) = 2 ∨
    Algebra.normalizedTrace ℚ L (z + z⁻¹) = -2 ∨
    Algebra.normalizedTrace ℚ L (z + z⁻¹) = 2 * ((p-1 : ℕ) : ℚ)⁻¹ := by
  have htwo : Algebra.normalizedTrace ℚ L 2 = 2 := by
    simpa using Algebra.normalizedTrace_algebraMap_apply ℚ ℚ L 2
  rcases double_prime_root_cases hp hp2 hz with h | h | h | h
  · right; left; norm_num [h, htwo]
  · right; right; left; norm_num [h, htwo]
  · left
    refine ⟨h, ?_⟩
    rw [map_add, normalizedTrace_primitive_root hp h, normalizedTrace_primitive_root hp h.inv]
    ring
  · right; right; right
    have ht := normalizedTrace_primitive_root hp h
    have hi := normalizedTrace_primitive_root hp h.inv
    simp only [inv_neg, map_neg] at ht hi
    rw [map_add]
    linarith

theorem primitive_pair_of_trace_sum {L : Type*} [Field L] [Algebra ℚ L]
    [Algebra.IsIntegral ℚ L] {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    {x y r s : L} (hx : IsPrimitiveRoot x p) (hy : IsPrimitiveRoot y p)
    (hr : r ^ (2*p) = 1) (hs : s ^ (2*p) = 1)
    (h : r + r⁻¹ + s + s⁻¹ = x + x⁻¹ + y + y⁻¹) :
    IsPrimitiveRoot r p ∧ IsPrimitiveRoot s p := by
  let d : ℚ := ((p-1 : ℕ) : ℚ)⁻¹
  have hnpos : (0 : ℚ) < ((p-1 : ℕ) : ℚ) := by exact_mod_cast (show 0 < p-1 by omega)
  have hd0 : 0 < d := inv_pos.mpr hnpos
  have hd1 : d < 1/3 := by
    have hn : (3 : ℚ) < ((p-1 : ℕ) : ℚ) := by exact_mod_cast (show 3 < p-1 by omega)
    have hmul : d * ((p-1 : ℕ) : ℚ) = 1 := inv_mul_cancel₀ hnpos.ne'
    nlinarith [mul_lt_mul_of_pos_left hn hd0]
  have ht := congrArg (Algebra.normalizedTrace ℚ L) h
  have heq : Algebra.normalizedTrace ℚ L (r + r⁻¹) +
      Algebra.normalizedTrace ℚ L (s + s⁻¹) = -4*d := by
    simp only [map_add, normalizedTrace_primitive_root hp hx, normalizedTrace_primitive_root hp hx.inv,
      normalizedTrace_primitive_root hp hy, normalizedTrace_primitive_root hp hy.inv] at ht ⊢
    dsimp [d]
    linarith
  rcases double_prime_trace_cases hp (by omega) hr with ⟨hrp, hrt⟩ | hrt | hrt | hrt <;>
    rcases double_prime_trace_cases hp (by omega) hs with ⟨hsp, hst⟩ | hst | hst | hst
  · exact ⟨hrp, hsp⟩
  all_goals change _ = _ at hrt hst; change _ = -4 * ((p-1 : ℕ) : ℚ)⁻¹ at heq
  all_goals dsimp [d] at hd0 hd1; linarith

end
end IsingBulk.PrimeFamily
