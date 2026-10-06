import IsingBulk.Algebra.SelectedPoint

/-! Nickel's equation with the manuscript's integer indices and first even order. -/
namespace IsingBulk.PrimeFamily
noncomputable section
open IntermediateField
open scoped IntermediateField

def NickelAt (s : ℂ) (n : ℕ) : Prop :=
  ‖s‖ = 1 ∧ ∃ l m : ℤ, s + s⁻¹ =
    (Real.cos (angle n l) : ℂ) + (Real.cos (angle n m) : ℂ)

theorem angleRoot_pow {n : ℕ} (hn : n ≠ 0) (l : ℤ) : angleRoot n l ^ n = 1 := by
  rw [angleRoot, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
  refine ⟨l, ?_⟩
  unfold angle
  push_cast
  field_simp

theorem cosine_mem_cyclotomic {n : ℕ} (hn : n ≠ 0) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ n) (l : ℤ) : (Real.cos (angle n l) : ℂ) ∈ ℚ⟮ζ⟯ := by
  have : NeZero n := ⟨hn⟩
  obtain ⟨i, _, hi⟩ := hζ.eq_pow_of_pow_eq_one (angleRoot_pow hn l)
  have hr : angleRoot n l ∈ ℚ⟮ζ⟯ := by
    rw [← hi]
    exact pow_mem (mem_adjoin_simple_self ℚ ζ) i
  have he : (Real.cos (angle n l) : ℂ) =
      (angleRoot n l + (angleRoot n l)⁻¹) / 2 := by
    have hh := exp_angle_add_inv (angle n l)
    change angleRoot n l + (angleRoot n l)⁻¹ = _ at hh
    rw [hh]
    ring
  rw [he]
  exact div_mem (add_mem hr (inv_mem hr)) (ofNat_mem _ _)

theorem cosineAverage_mem_cyclotomic {p : ℕ} (hp : p.Prime) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ p) (a b : ℤ) : (cosineAverage p a b : ℂ) ∈ ℚ⟮ζ⟯ := by
  unfold cosineAverage
  simp only [Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_ofNat]
  exact div_mem (add_mem (cosine_mem_cyclotomic hp.ne_zero hζ a)
    (cosine_mem_cyclotomic hp.ne_zero hζ b)) (ofNat_mem _ _)

theorem cosineAverage_not_rational {p : ℕ} (hp : p.Prime) {a b : ℤ}
    (ha : Admissible p a) (hb : Admissible p b) (q : ℚ) :
    (cosineAverage p a b : ℂ) ≠ (q : ℂ) := by
  intro hq
  have hqR : cosineAverage p a b = (q : ℝ) := by simpa using congrArg Complex.re hq
  have hq0 : (0 : ℚ) < q := by
    have := (cosineAverage_bounds ha hb).1
    rw [hqR] at this
    exact_mod_cast this
  let r : AlgebraicComplex := ⟨angleRoot p a,
    mem_algebraicClosure_iff'.mpr (((angleRoot_primitive hp ha).isIntegral hp.pos).tower_top)⟩
  let s : AlgebraicComplex := ⟨angleRoot p b,
    mem_algebraicClosure_iff'.mpr (((angleRoot_primitive hp hb).isIntegral hp.pos).tower_top)⟩
  have hr : IsPrimitiveRoot r p := by
    rw [← IsPrimitiveRoot.coe_submonoidClass_iff]
    exact angleRoot_primitive hp ha
  have hs : IsPrimitiveRoot s p := by
    rw [← IsPrimitiveRoot.coe_submonoidClass_iff]
    exact angleRoot_primitive hp hb
  apply primitive_sum_not_nonneg_rational hp hr hs (q := 4 * q) (by positivity)
  apply Subtype.ext
  change angleRoot p a + (angleRoot p a)⁻¹ + angleRoot p b + (angleRoot p b)⁻¹ = ((4*q : ℚ) : ℂ)
  have hra := exp_angle_add_inv (angle p a)
  have hrb := exp_angle_add_inv (angle p b)
  change angleRoot p a + (angleRoot p a)⁻¹ = _ at hra
  change angleRoot p b + (angleRoot p b)⁻¹ = _ at hrb
  calc
    _ = 4 * (cosineAverage p a b : ℂ) := by
      unfold cosineAverage
      simp only [Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_ofNat]
      linear_combination hra + hrb
    _ = _ := by rw [hq]; push_cast; ring

theorem selectedPoint_relation {p : ℕ} {a b : ℤ} (ha : Admissible p a) (hb : Admissible p b) :
    selectedPoint p a b + (selectedPoint p a b)⁻¹ = 2 * (cosineAverage p a b : ℂ) := by
  have hc := cosineAverage_bounds ha hb
  simpa only [selectedPoint, Real.cos_arccos (by linarith : -1 ≤ cosineAverage p a b) hc.2.le]
    using exp_angle_add_inv (Real.arccos (cosineAverage p a b))

theorem first_even_Nickel_order {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) {a b : ℤ}
    (ha : Admissible p a) (hb : Admissible p b) :
    NickelAt (selectedPoint p a b) (2*p) ∧
      ∀ n : ℕ, 0 < n → Even n → n < 2*p → ¬ NickelAt (selectedPoint p a b) n := by
  have hrel := selectedPoint_relation ha hb
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
      exact cosineAverage_not_rational hp ha hb q hq.symm
    apply not_mem_smaller_cyclotomic hp hp2 hn he hlt hζ hη hc hirr
    obtain ⟨_, l, m, hlm⟩ := hNickel
    have hcos := add_mem (cosine_mem_cyclotomic hn.ne' hη l) (cosine_mem_cyclotomic hn.ne' hη m)
    have heq : (cosineAverage p a b : ℂ) =
        ((Real.cos (angle n l) : ℂ) + (Real.cos (angle n m) : ℂ)) / 2 := by
      rw [← hlm, hrel]
      ring
    rw [heq]
    exact div_mem hcos (ofNat_mem _ _)

end
end IsingBulk.PrimeFamily
