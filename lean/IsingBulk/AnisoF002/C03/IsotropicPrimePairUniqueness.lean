import IsingBulk.AnisoF002.C03.IsotropicPrimeSparseRelation

/-!
# Uniqueness of the first pair on a dense prime subfamily

The exact six-term relation is treated with all signs and all roots.
Primes at least seven form the chosen dense obstruction family; this
choice does not truncate or restrict any physical particle series.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open scoped BigOperators

theorem isotropic_primitive_ne_inv {p : ℕ} (hp : 2 < p)
    {x : ℂ} (hx : IsPrimitiveRoot x p) : x ≠ x⁻¹ := by
  have hx0 : x ≠ 0 := hx.ne_zero (by omega)
  intro he
  have h2 : x ^ 2 = 1 := by
    calc
      x ^ 2 = x * x := pow_two x
      _ = x * x⁻¹ := congrArg (fun v => x * v) he
      _ = 1 := mul_inv_cancel₀ hx0
  exact (Nat.not_dvd_of_pos_of_lt (by omega : 0 < 2) hp)
    ((hx.pow_eq_one_iff_dvd 2).mp h2)

theorem isotropic_prime_signed_trace_unique {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    {x r s : ℂ} (hx : IsPrimitiveRoot x p) (hr : r ^ p = 1) (hs : s ^ p = 1)
    (ε η : ℤ) (hε : ε = 1 ∨ ε = -1) (hη : η = 1 ∨ η = -1)
    (he : 2 * (x + x⁻¹) = (ε : ℂ) * (r + r⁻¹) + (η : ℂ) * (s + s⁻¹)) :
    ε = 1 ∧ η = 1 ∧ r + r⁻¹ = x + x⁻¹ ∧ s + s⁻¹ = x + x⁻¹ := by
  classical
  let : NeZero p := ⟨hp.ne_zero⟩
  let one : Fin p := ⟨1, by omega⟩
  have hxinv : x⁻¹ ^ p = 1 := by rw [inv_pow, hx.pow_eq_one, inv_one]
  have hrinv : r⁻¹ ^ p = 1 := by rw [inv_pow, hr, inv_one]
  have hsinv : s⁻¹ ^ p = 1 := by rw [inv_pow, hs, inv_one]
  have index (v : ℂ) (hv : v ^ p = 1) : ∃ j : Fin p, x ^ j.val = v := by
    obtain ⟨j, hj, he⟩ := hx.eq_pow_of_pow_eq_one hv
    exact ⟨⟨j, hj⟩, he⟩
  obtain ⟨ix, hix⟩ := index x⁻¹ hxinv
  obtain ⟨ir, hir⟩ := index r hr
  obtain ⟨ir', hir'⟩ := index r⁻¹ hrinv
  obtain ⟨is, his⟩ := index s hs
  obtain ⟨is', his'⟩ := index s⁻¹ hsinv
  have hne := isotropic_primitive_ne_inv (by omega : 2 < p) hx
  have hix1 : ix ≠ one := by
    intro hi
    rw [hi] at hix
    exact hne (by simpa only [one, Fin.val_mk, pow_one] using hix)
  have not_both (v : ℂ) (j l : Fin p) (hj : x ^ j.val = v) (hl : x ^ l.val = v⁻¹) :
      ¬ (j = one ∧ l = one) := by
    rintro ⟨rfl, rfl⟩
    simp only [one, pow_one] at hj hl
    exact hne (hl.trans (congrArg Inv.inv hj.symm))
  let a : Fin 6 → ℤ := ![2, 2, -ε, -ε, -η, -η]
  let k : Fin 6 → Fin p := ![one, ix, ir, ir', is, is']
  have hrel : ∑ i, (a i : ℂ) * x ^ (k i).val = 0 := by
    norm_num [a, k, Fin.sum_univ_succ, one, hix, hir, hir', his, his']
    linear_combination he
  have hc := isotropic_prime_sparse_coefficients hp (by omega : 6 < p) hx a k hrel one
  simp [a, k, Fin.sum_univ_succ, hix1] at hc
  have hcc : (2 : ℤ) = (if ir = one then ε else 0) + (if ir' = one then ε else 0) +
      (if is = one then η else 0) + (if is' = one then η else 0) := by
    split_ifs at hc ⊢ <;> omega
  obtain ⟨hε1, hη1, hr1, hs1⟩ := isotropic_two_signed_pair_indicators ε η hε hη
    (ir = one) (ir' = one) (is = one) (is' = one)
    (not_both r ir ir' hir hir') (not_both s is is' his his') hcc
  have trace_eq (v : ℂ) (j l : Fin p) (hj : x ^ j.val = v) (hl : x ^ l.val = v⁻¹)
      (h : j = one ∨ l = one) : v + v⁻¹ = x + x⁻¹ := by
    rcases h with h | h
    · rw [h] at hj
      have hv : x = v := by simpa only [one, Fin.val_mk, pow_one] using hj
      rw [← hv]
    · rw [h] at hl
      have hv : x = v⁻¹ := by simpa only [one, Fin.val_mk, pow_one] using hl
      rw [hv, inv_inv, add_comm]
  exact ⟨hε1, hη1, trace_eq r ir ir' hir hir' hr1, trace_eq s is is' his his' hs1⟩

end
end IsingBulk.AnisoF002.Isotropic
