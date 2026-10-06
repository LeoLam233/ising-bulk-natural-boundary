import IsingBulk.Algebra.PrimeUniqueness
import IsingBulk.Algebra.PrimeDensity

/-! Source-facing endpoint for rc4 thm:prime. -/
namespace IsingBulk.PrimeFamily
noncomputable section
open Polynomial IntermediateField

theorem rootOfUnity_algebraic {n : ℕ} (hn : n ≠ 0) {z : ℂ} (hz : z^n = 1) :
    IsAlgebraic ℚ z := by
  apply IsIntegral.isAlgebraic
  refine ⟨X^n - 1, monic_X_pow_sub_one hn, ?_⟩
  simpa only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_one, sub_eq_zero] using hz

theorem unique_cosine_pair {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) {a b : ℤ}
    (ha : Admissible p a) (hb : Admissible p b) (l m : ℤ)
    (hrep : selectedPoint p a b + (selectedPoint p a b)⁻¹ =
      (Real.cos (angle (2*p) l) : ℂ) + (Real.cos (angle (2*p) m) : ℂ)) :
    (Real.cos (angle (2*p) l) = Real.cos (angle p a) ∧
      Real.cos (angle (2*p) m) = Real.cos (angle p b)) ∨
    (Real.cos (angle (2*p) l) = Real.cos (angle p b) ∧
      Real.cos (angle (2*p) m) = Real.cos (angle p a)) := by
  have hn : 2*p ≠ 0 := by omega
  let x : AlgebraicComplex := ⟨angleRoot p a,
    mem_algebraicClosure_iff'.mpr (((angleRoot_primitive hp ha).isIntegral hp.pos).tower_top)⟩
  let y : AlgebraicComplex := ⟨angleRoot p b,
    mem_algebraicClosure_iff'.mpr (((angleRoot_primitive hp hb).isIntegral hp.pos).tower_top)⟩
  let r : AlgebraicComplex := ⟨angleRoot (2*p) l,
    mem_algebraicClosure_iff.mpr (rootOfUnity_algebraic hn (angleRoot_pow hn l))⟩
  let s : AlgebraicComplex := ⟨angleRoot (2*p) m,
    mem_algebraicClosure_iff.mpr (rootOfUnity_algebraic hn (angleRoot_pow hn m))⟩
  have hx : IsPrimitiveRoot x p := by
    rw [← IsPrimitiveRoot.coe_submonoidClass_iff]
    exact angleRoot_primitive hp ha
  have hy : IsPrimitiveRoot y p := by
    rw [← IsPrimitiveRoot.coe_submonoidClass_iff]
    exact angleRoot_primitive hp hb
  have hr : r^(2*p) = 1 := Subtype.ext (angleRoot_pow hn l)
  have hs : s^(2*p) = 1 := Subtype.ext (angleRoot_pow hn m)
  have hsum : (Real.cos (angle (2*p) l) : ℂ) + (Real.cos (angle (2*p) m) : ℂ) =
      (Real.cos (angle p a) : ℂ) + (Real.cos (angle p b) : ℂ) := by
    rw [← hrep, selectedPoint_relation ha hb]
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

theorem selectedFamily_subset_arc {z : ℂ} (hz : z ∈ selectedFamily) :
    ∃ t : ℝ, 0 < t ∧ t < Real.pi / 2 ∧ z = Complex.exp ((t : ℂ) * Complex.I) := by
  obtain ⟨p, a, b, _, _, _, ha, hb, rfl⟩ := hz
  have hc := cosineAverage_bounds ha hb
  exact ⟨Real.arccos (cosineAverage p a b), Real.arccos_pos.mpr hc.2,
    Real.arccos_lt_pi_div_two.mpr hc.1, rfl⟩

/-- All five clauses of thm:prime, tied to the same selected family.
The first conjunct also records the given instance's membership in that family. -/
theorem prime_family {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) {a b : ℤ}
    (hab : a ≠ b) (ha : Admissible p a) (hb : Admissible p b) :
    selectedPoint p a b ∈ selectedFamily ∧
    (NickelAt (selectedPoint p a b) (2*p) ∧
      ∀ n : ℕ, 0 < n → Even n → n < 2*p → ¬ NickelAt (selectedPoint p a b) n) ∧
    (∀ l m : ℤ, selectedPoint p a b + (selectedPoint p a b)⁻¹ =
      (Real.cos (angle (2*p) l) : ℂ) + (Real.cos (angle (2*p) m) : ℂ) →
      (Real.cos (angle (2*p) l) = Real.cos (angle p a) ∧
        Real.cos (angle (2*p) m) = Real.cos (angle p b)) ∨
      (Real.cos (angle (2*p) l) = Real.cos (angle p b) ∧
        Real.cos (angle (2*p) m) = Real.cos (angle p a))) ∧
    (∀ t : ℝ, 0 < t → t < Real.pi / 2 → Complex.exp ((t : ℂ) * Complex.I) ∈ closure selectedFamily) ∧
    IsAlgebraic ℚ (selectedBranch p a b) ∧ ¬ IsOfFinOrder (selectedBranch p a b) :=
  ⟨⟨p, a, b, hp, hp11, hab, ha, hb, rfl⟩,
    first_even_Nickel_order hp (by omega) ha hb,
    unique_cosine_pair hp hp11 ha hb, fun _ ht htπ => selectedFamily_dense_arc ht htπ,
    selectedBranch_algebraic hp ha hb, selectedBranch_not_isOfFinOrder hp ha hb⟩

end
end IsingBulk.PrimeFamily
