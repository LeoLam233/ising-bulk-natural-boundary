import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.FieldTheory.LinearDisjoint

/-! Appendix A, lem:cyclotomic. Fields are embedded in a common ambient
characteristic-zero field; inf is intersection and bot is the rational field. -/

namespace IsingBulk
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Polynomial IntermediateField
open scoped IntermediateField

theorem cyclotomic_intersection {L : Type*} [Field L] [Algebra ℚ L]
    {p n : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n)
    {ζ η : L} (hζ : IsPrimitiveRoot ζ p) (hη : IsPrimitiveRoot η n) :
    (ℚ⟮ζ⟯ ⊓ ℚ⟮η⟯ : IntermediateField ℚ L) = ⊥ := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hn0 : n ≠ 0 := by intro h; exact hpn (h ▸ dvd_zero p)
  have : NeZero p := ⟨hp0⟩
  have : NeZero n := ⟨hn0⟩
  have hc : p.Coprime n := hp.coprime_iff_not_dvd.mpr hpn
  have hzint : IsIntegral ℚ ζ := (hζ.isIntegral hp.pos).tower_top
  have heint : IsIntegral ℚ η := (hη.isIntegral (Nat.pos_of_ne_zero hn0)).tower_top
  have := IntermediateField.adjoin.finiteDimensional hzint
  have := IntermediateField.adjoin.finiteDimensional heint
  have hzdeg : Module.finrank ℚ ℚ⟮ζ⟯ = p.totient := by
    rw [IntermediateField.adjoin.finrank hzint,
      ← hζ.minpoly_eq_cyclotomic_of_irreducible (cyclotomic.irreducible_rat hp.pos),
      natDegree_cyclotomic]
  have hedeg : Module.finrank ℚ ℚ⟮η⟯ = n.totient := by
    rw [IntermediateField.adjoin.finrank heint,
      ← hη.minpoly_eq_cyclotomic_of_irreducible (cyclotomic.irreducible_rat (Nat.pos_of_ne_zero hn0)),
      natDegree_cyclotomic]
  let S : IntermediateField ℚ L := ℚ⟮ζ⟯ ⊔ ℚ⟮η⟯
  have hfd : FiniteDimensional ℚ S := IntermediateField.finiteDimensional_sup _ _
  let z : S := ⟨ζ, (show ℚ⟮ζ⟯ ≤ S from le_sup_left) (IntermediateField.mem_adjoin_simple_self ℚ ζ)⟩
  let e : S := ⟨η, (show ℚ⟮η⟯ ≤ S from le_sup_right) (IntermediateField.mem_adjoin_simple_self ℚ η)⟩
  have hz : IsPrimitiveRoot z p := by
    rwa [← IsPrimitiveRoot.coe_submonoidClass_iff]
  have he : IsPrimitiveRoot e n := by
    rwa [← IsPrimitiveRoot.coe_submonoidClass_iff]
  have hlow := @IsPrimitiveRoot.lcm_totient_le_finrank ℚ S _ _ _ _
    (by convert! hfd; exact Subsingleton.elim _ _) p n z e hz he
    (cyclotomic.irreducible_rat (Nat.lcm_pos hp.pos (Nat.pos_of_ne_zero hn0)))
  rw [hc.lcm_eq_mul, Nat.totient_mul hc] at hlow
  apply IntermediateField.LinearDisjoint.inf_eq_bot
  apply IntermediateField.LinearDisjoint.of_finrank_sup
  apply le_antisymm (IntermediateField.finrank_sup_le _ _)
  rw [hzdeg, hedeg]
  convert! hlow
  exact Subsingleton.elim _ _

end IsingBulk
