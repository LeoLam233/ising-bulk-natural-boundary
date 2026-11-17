import IsingBulk.AnisoF002.C03.IsotropicPrimePairUniqueness
import IsingBulk.AnisoF002.C03.IsotropicPrimeGeometry

/-!
# Both first physical prime orders, including the negative HT sign

Every root competitor is included. The first odd order is treated in
both determinant signs; the first even order includes every 2p-th root.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section

theorem isotropic_signed_root_trace (ε : ℤ) (hε : ε = 1 ∨ ε = -1) (r : ℂ) :
    (ε : ℂ) * r + ((ε : ℂ) * r)⁻¹ = (ε : ℂ) * (r + r⁻¹) := by
  rcases hε with rfl | rfl <;> simp [mul_add]

theorem isotropic_twice_odd_root_decomposition {p : ℕ} (hp : Odd p)
    {y : ℂ} (hy : y ^ (2 * p) = 1) :
    ∃ (ε : ℤ) (r : ℂ), (ε = 1 ∨ ε = -1) ∧ r ^ p = 1 ∧ y = (ε : ℂ) * r := by
  have h2 : (y ^ p) ^ 2 = 1 := by rw [← pow_mul, Nat.mul_comm p 2]; exact hy
  rcases sq_eq_one_iff.mp h2 with h | h
  · exact ⟨1, y, Or.inl rfl, h, by simp⟩
  · refine ⟨-1, -y, Or.inr rfl, ?_, by simp⟩
    rw [neg_pow, hp.neg_one_pow, h]
    norm_num

theorem isotropic_prime_trace_unique {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    {x y z : ℂ} (hx : IsPrimitiveRoot x p) (hy : y ^ p = 1) (hz : z ^ p = 1)
    (he : 2 * (x + x⁻¹) = (y + y⁻¹) + (z + z⁻¹)) :
    y + y⁻¹ = x + x⁻¹ ∧ z + z⁻¹ = x + x⁻¹ := by
  have h := isotropic_prime_signed_trace_unique hp hp7 hx hy hz 1 1
    (Or.inl rfl) (Or.inl rfl) (by simpa only [Int.cast_one, one_mul] using he)
  exact h.2.2

theorem isotropic_twice_prime_trace_unique {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    {x y z : ℂ} (hx : IsPrimitiveRoot x p) (hy : y ^ (2 * p) = 1) (hz : z ^ (2 * p) = 1)
    (he : 2 * (x + x⁻¹) = (y + y⁻¹) + (z + z⁻¹)) :
    y + y⁻¹ = x + x⁻¹ ∧ z + z⁻¹ = x + x⁻¹ := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  obtain ⟨ε, r, hε, hr, hyr⟩ := isotropic_twice_odd_root_decomposition hodd hy
  obtain ⟨η, s, hη, hs, hzs⟩ := isotropic_twice_odd_root_decomposition hodd hz
  have he' : 2 * (x + x⁻¹) = (ε : ℂ) * (r + r⁻¹) + (η : ℂ) * (s + s⁻¹) := by
    simpa only [hyr, hzs, isotropic_signed_root_trace ε hε, isotropic_signed_root_trace η hη]
      using he
  obtain ⟨hε1, hη1, hrx, hsx⟩ := isotropic_prime_signed_trace_unique hp hp7 hx hr hs ε η hε hη he'
  constructor
  · simpa only [hyr, hε1, Int.cast_one, one_mul] using hrx
  · simpa only [hzs, hη1, Int.cast_one, one_mul] using hsx

theorem isotropic_negative_prime_trace_unique {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    {x y z : ℂ} (hx : IsPrimitiveRoot x p) (hy : y ^ p = -1) (hz : z ^ p = -1)
    (he : 2 * (-(x + x⁻¹)) = (y + y⁻¹) + (z + z⁻¹)) :
    y + y⁻¹ = -(x + x⁻¹) ∧ z + z⁻¹ = -(x + x⁻¹) := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hny : (-y) ^ p = 1 := by rw [neg_pow, hodd.neg_one_pow, hy]; norm_num
  have hnz : (-z) ^ p = 1 := by rw [neg_pow, hodd.neg_one_pow, hz]; norm_num
  have he' : 2 * (x + x⁻¹) = ((-y) + (-y)⁻¹) + ((-z) + (-z)⁻¹) := by
    simp only [inv_neg]
    linear_combination -he
  obtain ⟨h1, h2⟩ := isotropic_prime_trace_unique hp hp7 hx hny hnz he'
  simp only [inv_neg] at h1 h2
  constructor
  · linear_combination -h1
  · linear_combination -h2

theorem isotropic_negative_prime_trace_not_competitors {p n : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 0 < n) (hodd : Odd n) (hpn : ¬ p ∣ n)
    {x y z : ℂ} (hx : IsPrimitiveRoot x p) (hy : y ^ n = -1) (hz : z ^ n = -1) :
    2 * (-(x + x⁻¹)) ≠ (y + y⁻¹) + (z + z⁻¹) := by
  intro he
  have hny : (-y) ^ n = 1 := by rw [neg_pow, hodd.neg_one_pow, hy]; norm_num
  have hnz : (-z) ^ n = 1 := by rw [neg_pow, hodd.neg_one_pow, hz]; norm_num
  apply isotropic_prime_trace_not_competitors hp hp5 hn hpn hx hny hnz
  simp only [inv_neg]
  linear_combination -he

end
end IsingBulk.AnisoF002.Isotropic
