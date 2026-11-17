import IsingBulk.AnisoF002.C03.IsotropicCyclotomicAutomorphisms

/-!
# Exclusion of every lower cyclotomic competitor

A prime-order trace cannot be the average of two traces whose orders
are coprime to the prime.  The proof constructs the automorphism fixing
both competitors and squaring the prime root in their actual common
cyclotomic field.  This is F002's lower-particle arithmetic.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open scoped IntermediateField

theorem isotropic_prime_trace_not_competitors {p n : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 0 < n) (hpn : ¬ p ∣ n)
    {x y z : ℂ} (hx : IsPrimitiveRoot x p) (hy : y ^ n = 1) (hz : z ^ n = 1) :
    2 * (x + x⁻¹) ≠ (y + y⁻¹) + (z + z⁻¹) := by
  have hcop : p.Coprime n := hp.coprime_iff_not_dvd.mpr hpn
  let k := Nat.chineseRemainder hcop 2 1
  have hkp : k.val.Coprime p := by
    change Nat.gcd k.val p = 1
    rw [k.property.1.gcd_eq]
    exact (hp.coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt (by omega : 0 < 2) (by omega : 2 < p))).symm
  have hkn : k.val.Coprime n := by
    change Nat.gcd k.val n = 1
    rw [k.property.2.gcd_eq]
    exact Nat.gcd_one_left n
  have hk : k.val.Coprime (p * n) := hkp.mul_right hkn
  have hN : 0 < p * n := Nat.mul_pos hp.pos hn
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (p * n))
  have hζ : IsPrimitiveRoot ζ (p * n) := by
    simpa only [ζ, Nat.cast_mul] using Complex.isPrimitiveRoot_exp (p * n) hN.ne'
  let K := IntermediateField.adjoin ℚ {ζ}
  have hxN : x ^ (p * n) = 1 := by rw [pow_mul, hx.pow_eq_one, one_pow]
  have hyN : y ^ (p * n) = 1 := by rw [Nat.mul_comm p n, pow_mul, hy, one_pow]
  have hzN : z ^ (p * n) = 1 := by rw [Nat.mul_comm p n, pow_mul, hz, one_pow]
  let X : K := ⟨x, isotropic_root_mem_cyclotomic_adjoin hN hζ hxN⟩
  let Y : K := ⟨y, isotropic_root_mem_cyclotomic_adjoin hN hζ hyN⟩
  let Z : K := ⟨z, isotropic_root_mem_cyclotomic_adjoin hN hζ hzN⟩
  obtain ⟨f, hf⟩ := exists_isotropic_cyclotomic_power_automorphism hN hζ hk
  have hX : X ^ (p * n) = 1 := by apply Subtype.ext; exact hxN
  have hY : Y ^ (p * n) = 1 := by apply Subtype.ext; exact hyN
  have hZ : Z ^ (p * n) = 1 := by apply Subtype.ext; exact hzN
  have hfX : f X = X ^ 2 := by
    rw [hf X hX]
    apply Subtype.ext
    exact isotropic_root_pow_eq_of_modEq hx.pow_eq_one k.property.1
  have hfY : f Y = Y := by
    rw [hf Y hY]
    apply Subtype.ext
    exact (isotropic_root_pow_eq_of_modEq hy k.property.2).trans (pow_one y)
  have hfZ : f Z = Z := by
    rw [hf Z hZ]
    apply Subtype.ext
    exact (isotropic_root_pow_eq_of_modEq hz k.property.2).trans (pow_one z)
  intro he
  have heK : 2 * (X + X⁻¹) = (Y + Y⁻¹) + (Z + Z⁻¹) := by
    apply Subtype.ext
    exact he
  have heF := congrArg f heK
  simp only [map_mul, map_ofNat, map_add, map_inv₀, hfX, hfY, hfZ] at heF
  have ht : X + X⁻¹ = X ^ 2 + (X ^ 2)⁻¹ := by
    linear_combination (heK - heF) / 2
  apply isotropic_primitive_trace_ne_square_trace hp5 hx
  exact congrArg (fun a : K => (a : ℂ)) ht

end
end IsingBulk.AnisoF002.Isotropic
