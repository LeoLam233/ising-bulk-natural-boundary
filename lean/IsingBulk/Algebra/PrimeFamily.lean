import IsingBulk.Algebra.Cyclotomic
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic

/-!
Arithmetic steps of thm:prime. The source-facing endpoint is now
`PrimeTheorem.prime_family`, with cosine membership, uniqueness, density and branch nonresonance.
Normative definition: manuscript.tex, lines 329-336, pinned rc4 blob.
-/

namespace IsingBulk
namespace PrimeFamily
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Polynomial IntermediateField
open scoped IntermediateField

theorem prime_not_dvd_even_below_double {p n : ℕ} (hp : p.Prime) (hp2 : 2 < p)
    (hn : 0 < n) (hne : Even n) (hlt : n < 2*p) : ¬ p ∣ n := by
  intro hdiv
  obtain ⟨k, hk⟩ := hdiv
  have hkpos : 0 < k := by nlinarith
  have hklt : k < 2 := by nlinarith [hp.pos]
  have hk1 : k = 1 := by omega
  have hnp : n = p := by simpa [hk1] using hk
  have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
  have heven : n % 2 = 0 := Nat.even_iff.mp hne
  omega

/-- The smaller-order contradiction after the two field memberships and
nonrationality have been established. These hypotheses remain explicit. -/
theorem not_mem_smaller_cyclotomic {L : Type*} [Field L] [Algebra ℚ L]
    {p n : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hn : 0 < n)
    (hne : Even n) (hlt : n < 2*p)
    {ζ η c : L} (hζ : IsPrimitiveRoot ζ p) (hη : IsPrimitiveRoot η n)
    (hc : c ∈ ℚ⟮ζ⟯) (hirr : c ∉ (⊥ : IntermediateField ℚ L)) :
    c ∉ ℚ⟮η⟯ := by
  intro hcn
  apply hirr
  have hi : c ∈ (ℚ⟮ζ⟯ ⊓ ℚ⟮η⟯ : IntermediateField ℚ L) := ⟨hc, hcn⟩
  rwa [cyclotomic_intersection hp (prime_not_dvd_even_below_double hp hp2 hn hne hlt) hζ hη] at hi

/-- Minimal-polynomial form of the primitive-root trace calculation. -/
theorem trace_primitive_root {L : Type*} [Field L] [Algebra ℚ L]
    {p : ℕ} (hp : p.Prime) {ζ : L} (hζ : IsPrimitiveRoot ζ p) :
    Algebra.trace ℚ ℚ⟮ζ⟯ (IntermediateField.AdjoinSimple.gen ℚ ζ) = -1 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fact p.Prime := ⟨hp⟩
  have hm : -(minpoly ℚ ζ).nextCoeff = (-1 : ℚ) := by
    rw [← hζ.minpoly_eq_cyclotomic_of_irreducible (cyclotomic.irreducible_rat hp.pos)]
    congr 1
    rw [nextCoeff, ite_eq_right (by rw [natDegree_cyclotomic]; exact (Nat.totient_pos.mpr hp.pos).ne'),
      natDegree_cyclotomic, Nat.totient_prime hp, cyclotomic_prime]
    simp [coeff_X_pow, Finset.mem_range, show p-1-1 < p by have := hp.two_le; omega]
  convert! (trace_adjoinSimpleGen ((hζ.isIntegral hp.pos).tower_top : IsIntegral ℚ ζ)).trans hm
  all_goals exact Subsingleton.elim _ _

end PrimeFamily
end IsingBulk
