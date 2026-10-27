import IsingBulk.Algebra.PrimeTheorem

/-!
# LT22 Preferred: the equal-angle prime-root family

The prior source proves cyclotomic proper sublemmas for two admissible angles.
Here they are specialized to the manuscript's equal-angle point.  In particular,
the old selected-family endpoint, which requires distinct angles, is not used.
The trace estimate below is proved at the exact bound p ≥ 5 of LT22 Lemma 3.1.
-/

namespace IsingBulk.Preferred22
noncomputable section
open Polynomial IntermediateField IsingBulk.PrimeFamily

theorem primitive_pair_of_trace_sum_ge_five {L : Type*} [Field L] [Algebra ℚ L]
    [Algebra.IsIntegral ℚ L] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {x y r s : L} (hx : IsPrimitiveRoot x p) (hy : IsPrimitiveRoot y p)
    (hr : r ^ (2*p) = 1) (hs : s ^ (2*p) = 1)
    (h : r + r⁻¹ + s + s⁻¹ = x + x⁻¹ + y + y⁻¹) :
    IsPrimitiveRoot r p ∧ IsPrimitiveRoot s p := by
  let d : ℚ := ((p-1 : ℕ) : ℚ)⁻¹
  have hnpos : (0 : ℚ) < ((p-1 : ℕ) : ℚ) := by exact_mod_cast (show 0 < p-1 by omega)
  have hd0 : 0 < d := inv_pos.mpr hnpos
  have hd1 : d < 1/3 := by
    have hn : (3 : ℚ) < ((p-1 : ℕ) : ℚ) := by exact_mod_cast (show 3 < p-1 by omega)
    have hmul : d * ((p-1 : ℕ) : ℚ) = 1 := inv_mul_cancel₀ hnpos.ne'
    nlinarith [mul_lt_mul_of_pos_left hn hd0]
  have ht := congrArg (Algebra.normalizedTrace ℚ L) h
  have heq : Algebra.normalizedTrace ℚ L (r + r⁻¹) +
      Algebra.normalizedTrace ℚ L (s + s⁻¹) = -4*d := by
    simp only [map_add, normalizedTrace_primitive_root hp hx, normalizedTrace_primitive_root hp hx.inv,
      normalizedTrace_primitive_root hp hy, normalizedTrace_primitive_root hp hy.inv] at ht ⊢
    dsimp [d]
    linarith
  rcases double_prime_trace_cases hp (by omega) hr with ⟨hrp, hrt⟩ | hrt | hrt | hrt <;>
    rcases double_prime_trace_cases hp (by omega) hs with ⟨hsp, hst⟩ | hst | hst | hst
  · exact ⟨hrp, hsp⟩
  all_goals change _ = _ at hrt hst; change _ = -4 * ((p-1 : ℕ) : ℚ)⁻¹ at heq
  all_goals dsimp [d] at hd0 hd1; linarith


theorem unique_cosine_pair_ge_five {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {a b : ℤ}
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
  obtain ⟨hrp, hsp⟩ := primitive_pair_of_trace_sum_ge_five hp hp5 hx hy hr hs ht
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

/-- At equal angles the older selected point is exactly the primitive prime root. -/
theorem selectedPoint_diagonal {p : ℕ} {a : ℤ} (ha : Admissible p a) :
    selectedPoint p a a = angleRoot p a := by
  unfold selectedPoint cosineAverage angleRoot
  rw [show (Real.cos (angle p a) + Real.cos (angle p a)) / 2 =
      Real.cos (angle p a) by ring,
    Real.arccos_cos ha.1.le (by linarith [ha.2, Real.pi_pos])]

/-- The branch specified in the manuscript, with its actual exponential sign. -/
def primeBranch (p : ℕ) (a : ℤ) : ℂ :=
  Complex.exp (-(Real.arccos (2 * Real.cos (angle p a) - 1) : ℂ) * Complex.I)

theorem selectedBranch_diagonal (p : ℕ) (a : ℤ) :
    selectedBranch p a a = primeBranch p a := by
  unfold selectedBranch branchAngle cosineAverage primeBranch
  rw [show (Real.cos (angle p a) + Real.cos (angle p a)) / 2 =
    Real.cos (angle p a) by ring]

/-- The first *positive even* Nickel order is exactly 2p, including p=5 and p=7. -/
theorem prime_root_first_even {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {a : ℤ}
    (ha : Admissible p a) :
    NickelAt (angleRoot p a) (2*p) ∧
      ∀ n : ℕ, 0 < n → Even n → n < 2*p → ¬ NickelAt (angleRoot p a) n := by
  simpa only [selectedPoint_diagonal ha] using
    first_even_Nickel_order hp (by omega) ha ha

/-- The manuscript's unique equal cosine pair at the first even order. -/
theorem prime_root_unique_cosine_pair {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {a : ℤ}
    (ha : Admissible p a) (l m : ℤ)
    (hrep : angleRoot p a + (angleRoot p a)⁻¹ =
      (Real.cos (angle (2*p) l) : ℂ) + (Real.cos (angle (2*p) m) : ℂ)) :
    Real.cos (angle (2*p) l) = Real.cos (angle p a) ∧
      Real.cos (angle (2*p) m) = Real.cos (angle p a) := by
  have h := unique_cosine_pair_ge_five hp hp5 ha ha l m
    (by simpa only [selectedPoint_diagonal ha] using hrep)
  rcases h with h | h <;> exact h

/-- Algebraicity and nonresonance of ξ=exp(-i arccos(2 cos α-1)). -/
theorem prime_branch_algebraic_nonresonant {p : ℕ} (hp : p.Prime) {a : ℤ}
    (ha : Admissible p a) :
    IsAlgebraic ℚ (primeBranch p a) ∧ ¬ IsOfFinOrder (primeBranch p a) := by
  simpa only [selectedBranch_diagonal] using
    And.intro (selectedBranch_algebraic hp ha ha) (selectedBranch_not_isOfFinOrder hp ha ha)

/-- Positive separation for every fixed finite set of positive particle orders.
This is proved directly from nonresonance; no Diophantine tail bound is assumed. -/
theorem prime_branch_finite_separation {p : ℕ} (hp : p.Prime) {a : ℤ}
    (ha : Admissible p a) (M : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, 1 ≤ N → N ≤ M →
      δ ≤ ‖1 - primeBranch p a ^ N‖ := by
  have hnr := (prime_branch_algebraic_nonresonant hp ha).2
  have hpos (N : ℕ) (hN : 1 ≤ N) : 0 < ‖1 - primeBranch p a ^ N‖ := by
    apply norm_pos_iff.mpr
    intro hz
    apply hnr
    exact isOfFinOrder_iff_pow_eq_one.mpr
      ⟨N, by omega, (sub_eq_zero.mp hz).symm⟩
  induction M with
  | zero =>
      exact ⟨1, zero_lt_one, by intro N hN hNM; omega⟩
  | succ M ih =>
      obtain ⟨δ, hδ, hbound⟩ := ih
      refine ⟨min δ ‖1 - primeBranch p a ^ (M+1)‖,
        lt_min hδ (hpos (M+1) (by omega)), ?_⟩
      intro N hN hNM
      by_cases h : N ≤ M
      · exact (min_le_left _ _).trans (hbound N hN h)
      · have he : N = M+1 := by omega
        subst N
        exact min_le_right _ _

/-- The actual equal-angle family used in LT22; no unequal-angle restriction. -/
def primeRootFamily : Set ℂ :=
  {z | ∃ p : ℕ, ∃ a : ℤ, p.Prime ∧ 5 ≤ p ∧ Admissible p a ∧ z = angleRoot p a}

/-- Density of the exact family in every open first-quadrant unit-circle arc. -/
theorem prime_root_family_dense_arc {t : ℝ} (ht : 0 < t) (htπ : t < Real.pi / 2) :
    Complex.exp ((t : ℂ) * Complex.I) ∈ closure primeRootFamily := by
  let f : ℝ → ℂ := fun u => Complex.exp ((u : ℂ) * Complex.I)
  have hf : Continuous f := Complex.continuous_exp.comp
    (Complex.continuous_ofReal.mul_const Complex.I)
  change f t ∈ closure primeRootFamily
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.mp hf.continuousAt ε hε
  obtain ⟨p, a, b, hp, hp11, hab, ha, hb, hea, heb⟩ :=
    neighboring_prime_angles ht htπ hδ
  refine ⟨angleRoot p a, ⟨p, a, hp, by omega, ha, rfl⟩, ?_⟩
  rw [dist_comm]
  exact hcont (by simpa only [Real.dist_eq] using hea)

/-- Integer inequalities in the manuscript imply the angular admissibility predicate. -/
theorem admissible_of_quarter_bounds {p : ℕ} (hp : 0 < p) {a : ℤ}
    (ha : 1 ≤ a) (ha4 : 4*a < p) : Admissible p a := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have haR : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have ha4R : 4*(a : ℝ) < p := by exact_mod_cast ha4
  unfold Admissible angle
  constructor
  · exact div_pos (mul_pos (by positivity) haR) hpR
  · apply (div_lt_iff₀ hpR).mpr
    nlinarith [mul_pos Real.pi_pos (sub_pos.mpr ha4R)]

/-- Lemma 3.1, all arithmetic conclusions at the frozen scope.
The density conjunct uses the same primeRootFamily, whose defining primes are ≥ 5. -/
theorem manuscript_prime_root_family {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {a : ℤ}
    (ha1 : 1 ≤ a) (ha4 : 4*a < p) :
    angleRoot p a ∈ primeRootFamily ∧
    (NickelAt (angleRoot p a) (2*p) ∧
      ∀ n : ℕ, 0 < n → Even n → n < 2*p → ¬ NickelAt (angleRoot p a) n) ∧
    (∀ l m : ℤ, angleRoot p a + (angleRoot p a)⁻¹ =
      (Real.cos (angle (2*p) l) : ℂ) + (Real.cos (angle (2*p) m) : ℂ) →
      Real.cos (angle (2*p) l) = Real.cos (angle p a) ∧
      Real.cos (angle (2*p) m) = Real.cos (angle p a)) ∧
    (∀ t : ℝ, 0 < t → t < Real.pi / 2 →
      Complex.exp ((t : ℂ) * Complex.I) ∈ closure primeRootFamily) ∧
    IsAlgebraic ℚ (primeBranch p a) ∧ ¬ IsOfFinOrder (primeBranch p a) := by
  have ha := admissible_of_quarter_bounds hp.pos ha1 ha4
  exact ⟨⟨p, a, hp, hp5, ha, rfl⟩,
    prime_root_first_even hp hp5 ha,
    prime_root_unique_cosine_pair hp hp5 ha,
    fun _ ht htπ => prime_root_family_dense_arc ht htπ,
    (prime_branch_algebraic_nonresonant hp ha).1,
    (prime_branch_algebraic_nonresonant hp ha).2⟩

end
end IsingBulk.Preferred22
