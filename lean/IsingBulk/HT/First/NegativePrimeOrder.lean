import IsingBulk.HT.First.NegativePrimeFamily
import IsingBulk.HT.First.PrimeOrder

/-! Actual prime-order classification on the negative-cosine family.
The cyclotomic-intersection and trace-uniqueness proofs are reused from LT;
the new second-moment trace supplies the missing irrationality hypothesis. -/
namespace IsingBulk.HT.First
noncomputable section
open IsingBulk.PrimeFamily Polynomial IntermediateField
open scoped IntermediateField

theorem negative_first_even_Nickel_order {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) {a b : ℤ}
    (ha : NegativeAdmissible p a) (hb : NegativeAdmissible p b) :
    NickelAt (selectedPoint p a b) (2*p) ∧
      ∀ n : ℕ, 0 < n → Even n → n < 2*p → ¬ NickelAt (selectedPoint p a b) n := by
  have hrel := negative_selectedPoint_relation ha hb
  constructor
  · refine ⟨Complex.norm_exp_ofReal_mul_I _, 2*a, 2*b, ?_⟩
    have hang (j : ℤ) : angle (2*p) (2*j) = angle p j := by
      unfold angle
      push_cast
      ring
    rw [hang, hang, hrel]
    unfold cosineAverage
    push_cast
    ring
  · intro n hn he hlt hNickel
    let ζ := Complex.exp (2 * Real.pi * Complex.I / p)
    let η := Complex.exp (2 * Real.pi * Complex.I / n)
    have hζ := Complex.isPrimitiveRoot_exp p hp.ne_zero
    have hη := Complex.isPrimitiveRoot_exp n hn.ne'
    have hc := cosineAverage_mem_cyclotomic hp hζ a b
    have hirr : (cosineAverage p a b : ℂ) ∉ (⊥ : IntermediateField ℚ ℂ) := by
      intro hh
      obtain ⟨q, hq⟩ := mem_bot.mp hh
      exact negative_cosineAverage_not_rational hp hp11 ha hb q hq.symm
    apply not_mem_smaller_cyclotomic hp (by omega) hn he hlt hζ hη hc hirr
    obtain ⟨_, l, m, hlm⟩ := hNickel
    have hcos := add_mem (cosine_mem_cyclotomic hn.ne' hη l) (cosine_mem_cyclotomic hn.ne' hη m)
    have heq : (cosineAverage p a b : ℂ) =
        ((Real.cos (angle n l) : ℂ) + (Real.cos (angle n m) : ℂ)) / 2 := by
      rw [← hlm, hrel]
      ring
    rw [heq]
    exact div_mem hcos (ofNat_mem _ _)


theorem negative_unique_cosine_pair {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) {a b : ℤ}
    (ha : NegativeAdmissible p a) (hb : NegativeAdmissible p b) (l m : ℤ)
    (hrep : selectedPoint p a b + (selectedPoint p a b)⁻¹ =
      (Real.cos (angle (2*p) l) : ℂ) + (Real.cos (angle (2*p) m) : ℂ)) :
    (Real.cos (angle (2*p) l) = Real.cos (angle p a) ∧
      Real.cos (angle (2*p) m) = Real.cos (angle p b)) ∨
    (Real.cos (angle (2*p) l) = Real.cos (angle p b) ∧
      Real.cos (angle (2*p) m) = Real.cos (angle p a)) := by
  have hn : 2*p ≠ 0 := by omega
  let x : AlgebraicComplex := ⟨angleRoot p a,
    mem_algebraicClosure_iff'.mpr (((negative_angleRoot_primitive hp ha).isIntegral hp.pos).tower_top)⟩
  let y : AlgebraicComplex := ⟨angleRoot p b,
    mem_algebraicClosure_iff'.mpr (((negative_angleRoot_primitive hp hb).isIntegral hp.pos).tower_top)⟩
  let r : AlgebraicComplex := ⟨angleRoot (2*p) l,
    mem_algebraicClosure_iff.mpr (rootOfUnity_algebraic hn (angleRoot_pow hn l))⟩
  let s : AlgebraicComplex := ⟨angleRoot (2*p) m,
    mem_algebraicClosure_iff.mpr (rootOfUnity_algebraic hn (angleRoot_pow hn m))⟩
  have hx : IsPrimitiveRoot x p := by
    rw [← IsPrimitiveRoot.coe_submonoidClass_iff]
    exact negative_angleRoot_primitive hp ha
  have hy : IsPrimitiveRoot y p := by
    rw [← IsPrimitiveRoot.coe_submonoidClass_iff]
    exact negative_angleRoot_primitive hp hb
  have hr : r^(2*p) = 1 := Subtype.ext (angleRoot_pow hn l)
  have hs : s^(2*p) = 1 := Subtype.ext (angleRoot_pow hn m)
  have hsum : (Real.cos (angle (2*p) l) : ℂ) + (Real.cos (angle (2*p) m) : ℂ) =
      (Real.cos (angle p a) : ℂ) + (Real.cos (angle p b) : ℂ) := by
    rw [← hrep, negative_selectedPoint_relation ha hb]
    unfold cosineAverage
    push_cast
    ring
  have ht : r + r⁻¹ + s + s⁻¹ = x + x⁻¹ + y + y⁻¹ := by
    apply Subtype.ext
    change angleRoot (2*p) l + (angleRoot (2*p) l)⁻¹ +
      angleRoot (2*p) m + (angleRoot (2*p) m)⁻¹ =
      angleRoot p a + (angleRoot p a)⁻¹ + angleRoot p b + (angleRoot p b)⁻¹
    have hl := exp_angle_add_inv (angle (2*p) l)
    have hm := exp_angle_add_inv (angle (2*p) m)
    have ha' := exp_angle_add_inv (angle p a)
    have hb' := exp_angle_add_inv (angle p b)
    change angleRoot (2*p) l + (angleRoot (2*p) l)⁻¹ = _ at hl
    change angleRoot (2*p) m + (angleRoot (2*p) m)⁻¹ = _ at hm
    change angleRoot p a + (angleRoot p a)⁻¹ = _ at ha'
    change angleRoot p b + (angleRoot p b)⁻¹ = _ at hb'
    linear_combination hl + hm - ha' - hb' + 2 * hsum
  obtain ⟨hrp, hsp⟩ := primitive_pair_of_trace_sum hp hp11 hx hy hr hs ht
  have hchoice := primitive_trace_pair_unique hp hx hy hrp hsp ht
  have bridge (j : ℤ) (hh : r + r⁻¹ = (⟨angleRoot p j,
      mem_algebraicClosure_iff.mpr (rootOfUnity_algebraic hp.ne_zero (angleRoot_pow hp.ne_zero j))⟩ :
      AlgebraicComplex) + (⟨angleRoot p j,
      mem_algebraicClosure_iff.mpr (rootOfUnity_algebraic hp.ne_zero (angleRoot_pow hp.ne_zero j))⟩ :
      AlgebraicComplex)⁻¹) : Real.cos (angle (2*p) l) = Real.cos (angle p j) := by
    have hc := congrArg (fun z : AlgebraicComplex => (z : ℂ)) hh
    change angleRoot (2*p) l + (angleRoot (2*p) l)⁻¹ = angleRoot p j + (angleRoot p j)⁻¹ at hc
    unfold angleRoot at hc
    rw [exp_angle_add_inv, exp_angle_add_inv] at hc
    exact Complex.ofReal_injective (mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) hc)
  have hsumR := congrArg Complex.re hsum
  simp only [Complex.add_re, Complex.ofReal_re] at hsumR
  rcases hchoice with hchoice | hchoice
  · have hl := bridge a hchoice
    exact Or.inl ⟨hl, by linarith⟩
  · have hl := bridge b hchoice
    exact Or.inr ⟨hl, by linarith⟩

theorem negative_first_prime_Nickel_order {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    {a b : ℤ} (ha : NegativeAdmissible p a) (hb : NegativeAdmissible p b) :
    Odd p ∧ NickelAt (selectedPoint p a b) p ∧
      ∀ n : ℕ, 0 < n → n < p → ¬ NickelAt (selectedPoint p a b) n := by
  refine ⟨hp.odd_of_ne_two (by omega), ?_, ?_⟩
  · refine ⟨Complex.norm_exp_ofReal_mul_I _,a,b,?_⟩
    rw [negative_selectedPoint_relation ha hb]
    unfold cosineAverage
    push_cast
    ring
  · intro n hn hnp hNickel
    apply (negative_first_even_Nickel_order hp hp11 ha hb).2 (2*n)
      (by omega) ⟨n,by omega⟩ (by omega)
    exact nickel_double_order hNickel

/-- The established unique pair result specializes from 2p to p by label
inclusion, without changing its cyclotomic proof. -/
theorem negative_unique_prime_cosine_pair {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    {a b : ℤ} (ha : NegativeAdmissible p a) (hb : NegativeAdmissible p b) (l m : ℤ)
    (hrep : selectedPoint p a b+(selectedPoint p a b)⁻¹ =
      (Real.cos (angle p l) : ℂ)+(Real.cos (angle p m) : ℂ)) :
    (Real.cos (angle p l) = Real.cos (angle p a) ∧
      Real.cos (angle p m) = Real.cos (angle p b)) ∨
    (Real.cos (angle p l) = Real.cos (angle p b) ∧
      Real.cos (angle p m) = Real.cos (angle p a)) := by
  have h := negative_unique_cosine_pair hp hp11 ha hb (2*l) (2*m)
    (by simpa only [angle_double_order] using hrep)
  simpa only [angle_double_order] using h


end
end IsingBulk.HT.First
