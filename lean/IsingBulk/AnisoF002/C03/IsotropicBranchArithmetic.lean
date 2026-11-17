import IsingBulk.AnisoF002.C03.IsotropicCyclotomicAutomorphisms

/-!
# The branch-mean gap from genuine cyclotomic embeddings

An arbitrary root-of-unity extension admits a lift of each primitive
prime-root conjugacy.  A negative conjugate then contradicts the real
part bound of a unit-root trace.  No branch gap is assumed.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open scoped IntermediateField

theorem exists_isotropic_coprime_lift {p N a : ℕ} (hN : 0 < N)
    (hpN : p ∣ N) (ha : a.Coprime p) :
    ∃ k : ℕ, k.Coprime N ∧ k ≡ a [MOD p] := by
  let : NeZero N := ⟨hN.ne'⟩
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective hpN (ZMod.unitOfCoprime a ha)
  refine ⟨(u : ZMod N).val, ZMod.val_coe_unit_coprime u, ?_⟩
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  rw [ZMod.natCast_val]
  simpa only [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime] using
    congrArg (fun v : (ZMod p)ˣ => (v : ZMod p)) hu

theorem isotropic_primitive_trace_branch_gap {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {x y ξ : ℂ} (hx : IsPrimitiveRoot x p) (hy : IsPrimitiveRoot y p)
    (δ : ℚ) (hnegative : ((δ : ℂ) * (y + y⁻¹)).re < 0)
    (hrelation : ξ + ξ⁻¹ = 2 * ((δ : ℂ) * (x + x⁻¹)) - 2) :
    ξ ^ q ≠ 1 := by
  let : NeZero p := ⟨hp.ne'⟩
  obtain ⟨a, _, ha⟩ := hx.eq_pow_of_pow_eq_one hy.pow_eq_one
  have hac : a.Coprime p := (hx.pow_iff_coprime hp a).mp (ha.symm ▸ hy)
  have hN : 0 < p * q := Nat.mul_pos hp hq
  obtain ⟨k, hk, hka⟩ := exists_isotropic_coprime_lift hN (dvd_mul_right p q) hac
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((p * q : ℕ) : ℂ))
  have hζ : IsPrimitiveRoot ζ (p * q) := Complex.isPrimitiveRoot_exp _ hN.ne'
  let K := IntermediateField.adjoin ℚ {ζ}
  have hxN : x ^ (p * q) = 1 := by rw [pow_mul, hx.pow_eq_one, one_pow]
  intro hξ
  have hξN : ξ ^ (p * q) = 1 := by rw [Nat.mul_comm p q, pow_mul, hξ, one_pow]
  let X : K := ⟨x, isotropic_root_mem_cyclotomic_adjoin hN hζ hxN⟩
  let R : K := ⟨ξ, isotropic_root_mem_cyclotomic_adjoin hN hζ hξN⟩
  obtain ⟨f, hf⟩ := exists_isotropic_cyclotomic_power_automorphism hN hζ hk
  have hX : X ^ (p * q) = 1 := by apply Subtype.ext; exact hxN
  have hfX : (f X : ℂ) = y := by
    rw [hf X hX]
    change x ^ k = y
    exact (isotropic_root_pow_eq_of_modEq hx.pow_eq_one hka).trans ha
  have hR : R ^ q = 1 := by apply Subtype.ext; exact hξ
  have hfR : (f R : ℂ) ^ q = 1 := by
    have h : (f R) ^ q = 1 := by simpa only [map_pow, map_one] using congrArg f hR
    exact_mod_cast h
  have heK : R + R⁻¹ = 2 * ((δ : K) * (X + X⁻¹)) - 2 := by
    apply Subtype.ext
    exact hrelation
  have he := congrArg (fun v : K => (f v : ℂ)) heK
  simp only [map_add, map_inv₀, map_sub, map_mul, map_ofNat, map_ratCast] at he
  change (f R : ℂ) + (f R : ℂ)⁻¹ =
    2 * ((δ : ℂ) * ((f X : ℂ) + (f X : ℂ)⁻¹)) - 2 at he
  rw [hfX] at he
  have hn : ‖(f R : ℂ)‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hfR hq.ne'
  have hninv : ‖(f R : ℂ)⁻¹‖ = 1 := by rw [norm_inv, hn, inv_one]
  have hr := (abs_le.mp (Complex.abs_re_le_norm (f R : ℂ))).1
  have hri := (abs_le.mp (Complex.abs_re_le_norm ((f R : ℂ)⁻¹))).1
  have her := congrArg Complex.re he
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re,
    show (2 : ℂ).re = 2 from rfl, show (2 : ℂ).im = 0 from rfl,
    zero_mul, sub_zero] at her hnegative
  rw [hn] at hr
  rw [hninv] at hri
  linarith

end
end IsingBulk.AnisoF002.Isotropic
