import IsingBulk.AnisoF002.C03.IsotropicCyclotomicAutomorphisms

/-!
# Exact sparse cyclotomic coefficient extraction

The first-pair relation has six monomials. For each prime at least seven,
an unused coefficient and the prime cyclotomic polynomial force every
coefficient of that actual relation to vanish. This dense prime subfamily
is used only to choose obstructions; all physical particles are retained.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open scoped BigOperators

theorem isotropic_prime_sparse_coefficients {p m : ℕ} (hp : p.Prime) (hmp : m < p)
    {x : ℂ} (hx : IsPrimitiveRoot x p) (a : Fin m → ℤ) (k : Fin m → Fin p)
    (hrel : ∑ i, (a i : ℂ) * x ^ (k i).val = 0) :
    ∀ j : Fin p, (∑ i, if k i = j then a i else 0) = 0 := by
  classical
  let c : Fin p → ℤ := fun j => ∑ i, if k i = j then a i else 0
  have hc : ∑ j, (c j : ℂ) * x ^ j.val = 0 := by
    simp only [c, Int.cast_sum, Int.cast_ite, Int.cast_zero, Finset.sum_mul]
    rw [Finset.sum_comm]
    simpa using hrel
  have hall := (hx.sum_eq_zero_iff_forall_eq_int hp c).mp hc
  have hcard : (Finset.univ.image k).card < (Finset.univ : Finset (Fin p)).card := by
    calc
      (Finset.univ.image k).card ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_image_le
      _ < (Finset.univ : Finset (Fin p)).card := by simpa using hmp
  obtain ⟨j₀, _, hj₀⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hzero : c j₀ = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hne : k i ≠ j₀ := by
      intro he
      exact hj₀ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, he⟩)
    simp only [hne, ite_false]
  intro j
  exact (hall j j₀).trans hzero

theorem isotropic_two_signed_pair_indicators
    (ε η : ℤ) (hε : ε = 1 ∨ ε = -1) (hη : η = 1 ∨ η = -1)
    (A A' B B' : Prop) [Decidable A] [Decidable A'] [Decidable B] [Decidable B']
    (hA : ¬ (A ∧ A')) (hB : ¬ (B ∧ B'))
    (h : 2 = (if A then ε else 0) + (if A' then ε else 0) +
      (if B then η else 0) + (if B' then η else 0)) :
    ε = 1 ∧ η = 1 ∧ (A ∨ A') ∧ (B ∨ B') := by
  by_cases ha : A <;> by_cases ha' : A' <;> by_cases hb : B <;> by_cases hb' : B'
  all_goals simp_all
  all_goals omega

end
end IsingBulk.AnisoF002.Isotropic
