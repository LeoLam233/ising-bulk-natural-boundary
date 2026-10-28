import IsingBulk.HT22.Arithmetic.TraceArithmetic
import IsingBulk.Preferred22.Arithmetic

/-! F001 Lemma 3.1: the full upper-half equal-angle prime family. -/
namespace IsingBulk.HT22.Arithmetic
noncomputable section
open Polynomial IntermediateField IsingBulk.PrimeFamily
open scoped IntermediateField

/-- Exactly the integer range `1 ≤ a ≤ (p−1)/2`, without natural division. -/
def PrimeIndex (p : ℕ) (a : ℤ) : Prop := 1 ≤ a ∧ 2*a < p

theorem primeIndex_angle_bounds {p : ℕ} (hp : 0<p) {a : ℤ} (ha : PrimeIndex p a) :
    0 < angle p a ∧ angle p a < Real.pi := by
  have hpR : (0:ℝ)<p := by exact_mod_cast hp
  have haR : (0:ℝ)<a := by exact_mod_cast (show 0<a from lt_of_lt_of_le (by norm_num) ha.1)
  have ha2R : 2*(a:ℝ)<p := by exact_mod_cast ha.2
  unfold angle
  constructor
  · exact div_pos (mul_pos (by positivity) haR) hpR
  · apply (div_lt_iff₀ hpR).mpr
    nlinarith [mul_pos Real.pi_pos (sub_pos.mpr ha2R)]

theorem primeIndex_primitive {p : ℕ} (hp : p.Prime) {a : ℤ} (ha : PrimeIndex p a) :
    IsPrimitiveRoot (angleRoot p a) p := by
  have ha0 : 0<a := by have := ha.1; omega
  have hap : a<(p:ℤ) := by have := ha.2; omega
  have hn : a.natAbs<p := by
    have hh : (a.natAbs:ℤ)<p := by rw [Int.natCast_natAbs, abs_of_pos ha0]; exact hap
    exact_mod_cast hh
  have hz : a.natAbs≠0 := Int.natAbs_ne_zero.mpr ha0.ne'
  have hc : IsCoprime a (p:ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast]
    exact (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hz) hn)).symm
  convert Complex.isPrimitiveRoot_exp_of_isCoprime a p hp.ne_zero hc using 1
  unfold angleRoot angle
  push_cast
  congr 1
  ring

theorem primeRoot_trace_not_rational {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : PrimeIndex p a) (q : ℚ) :
    angleRoot p a+(angleRoot p a)⁻¹ ≠ (q:ℂ) := by
  let r : AlgebraicComplex := ⟨angleRoot p a,
    mem_algebraicClosure_iff'.mpr (((primeIndex_primitive hp ha).isIntegral hp.pos).tower_top)⟩
  have hr : IsPrimitiveRoot r p := by
    rw [← IsPrimitiveRoot.coe_submonoidClass_iff]
    exact primeIndex_primitive hp ha
  intro h
  apply primitive_trace_not_rational hp hp5 hr q
  exact Subtype.ext h

/-- No positive particle order below p can satisfy the Nickel equation;
this is stronger than the odd-order exclusion used in F001. -/
theorem primeRoot_first_order {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : PrimeIndex p a) :
    Odd p ∧ NickelAt (angleRoot p a) p ∧
      ∀ n : ℕ, 0<n → n<p → ¬ NickelAt (angleRoot p a) n := by
  refine ⟨hp.odd_of_ne_two (by omega), ?_, ?_⟩
  · refine ⟨Complex.norm_exp_ofReal_mul_I _,a,a,?_⟩
    have h := exp_angle_add_inv (angle p a)
    change angleRoot p a+(angleRoot p a)⁻¹=_ at h
    rw [h]
    ring
  · intro n hn hnp hNickel
    let ζ := angleRoot p a
    let η := Complex.exp (2*Real.pi*Complex.I/n)
    have hζ := primeIndex_primitive hp ha
    have hη := Complex.isPrimitiveRoot_exp n hn.ne'
    have hc : ζ+ζ⁻¹ ∈ ℚ⟮ζ⟯ :=
      add_mem (mem_adjoin_simple_self ℚ ζ) (inv_mem (mem_adjoin_simple_self ℚ ζ))
    have hcn : ζ+ζ⁻¹ ∈ ℚ⟮η⟯ := by
      obtain ⟨_,l,m,hlm⟩ := hNickel
      rw [hlm]
      exact add_mem (cosine_mem_cyclotomic hn.ne' hη l) (cosine_mem_cyclotomic hn.ne' hη m)
    have hbot : ζ+ζ⁻¹ ∈ (⊥ : IntermediateField ℚ ℂ) := by
      have hh : ζ+ζ⁻¹ ∈ (ℚ⟮ζ⟯ ⊓ ℚ⟮η⟯ : IntermediateField ℚ ℂ) := ⟨hc,hcn⟩
      rwa [IsingBulk.cyclotomic_intersection hp (Nat.not_dvd_of_pos_of_lt hn hnp) hζ hη] at hh
    obtain ⟨q,hq⟩ := mem_bot.mp hbot
    exact primeRoot_trace_not_rational hp hp5 ha q hq.symm

/-- The unique equal cosine pair at p, for both signs of the cosine. -/
theorem primeRoot_unique_cosine_pair {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : PrimeIndex p a) (l m : ℤ)
    (hrep : angleRoot p a+(angleRoot p a)⁻¹ =
      (Real.cos (angle p l):ℂ)+(Real.cos (angle p m):ℂ)) :
    Real.cos (angle p l)=Real.cos (angle p a) ∧
      Real.cos (angle p m)=Real.cos (angle p a) := by
  let x : AlgebraicComplex := ⟨angleRoot p a,
    mem_algebraicClosure_iff'.mpr (((primeIndex_primitive hp ha).isIntegral hp.pos).tower_top)⟩
  let r : AlgebraicComplex := ⟨angleRoot p l,
    mem_algebraicClosure_iff.mpr (rootOfUnity_algebraic hp.ne_zero (angleRoot_pow hp.ne_zero l))⟩
  let s : AlgebraicComplex := ⟨angleRoot p m,
    mem_algebraicClosure_iff.mpr (rootOfUnity_algebraic hp.ne_zero (angleRoot_pow hp.ne_zero m))⟩
  have hx : IsPrimitiveRoot x p := by
    rw [← IsPrimitiveRoot.coe_submonoidClass_iff]
    exact primeIndex_primitive hp ha
  have hr : r^(2*p)=1 := by
    apply Subtype.ext
    change (angleRoot p l)^(2*p)=1
    rw [Nat.mul_comm 2 p,pow_mul,angleRoot_pow hp.ne_zero l,one_pow]
  have hs : s^(2*p)=1 := by
    apply Subtype.ext
    change (angleRoot p m)^(2*p)=1
    rw [Nat.mul_comm 2 p,pow_mul,angleRoot_pow hp.ne_zero m,one_pow]
  have ht : r+r⁻¹+s+s⁻¹=x+x⁻¹+x+x⁻¹ := by
    apply Subtype.ext
    change angleRoot p l+(angleRoot p l)⁻¹+angleRoot p m+(angleRoot p m)⁻¹ =
      angleRoot p a+(angleRoot p a)⁻¹+angleRoot p a+(angleRoot p a)⁻¹
    have hl := exp_angle_add_inv (angle p l)
    have hm := exp_angle_add_inv (angle p m)
    change angleRoot p l+(angleRoot p l)⁻¹=_ at hl
    change angleRoot p m+(angleRoot p m)⁻¹=_ at hm
    linear_combination hl+hm-2*hrep
  obtain ⟨hrp,hsp⟩ := IsingBulk.Preferred22.primitive_pair_of_trace_sum_ge_five hp hp5 hx hx hr hs ht
  have hchoice := primitive_trace_pair_unique hp hx hx hrp hsp ht
  have he : r+r⁻¹=x+x⁻¹ := hchoice.elim id id
  have hc := congrArg (fun z : AlgebraicComplex => (z:ℂ)) he
  change angleRoot p l+(angleRoot p l)⁻¹=angleRoot p a+(angleRoot p a)⁻¹ at hc
  unfold angleRoot at hc
  rw [exp_angle_add_inv,exp_angle_add_inv] at hc
  have hl : Real.cos (angle p l)=Real.cos (angle p a) :=
    Complex.ofReal_injective (mul_left_cancel₀ (by norm_num : (2:ℂ)≠0) hc)
  refine ⟨hl,?_⟩
  have ha' := exp_angle_add_inv (angle p a)
  change angleRoot p a+(angleRoot p a)⁻¹=_ at ha'
  rw [ha'] at hrep
  have hsum := congrArg Complex.re hrep
  simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.re_ofNat,Complex.im_ofNat,mul_zero,sub_zero] at hsum
  rw [hl] at hsum
  linarith

end
end IsingBulk.HT22.Arithmetic
