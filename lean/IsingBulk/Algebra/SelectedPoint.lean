import IsingBulk.Algebra.BranchArithmetic

/-! Exact prime-family parameters, rc4 manuscript lines 345–392. -/
namespace IsingBulk.PrimeFamily
noncomputable section
open Polynomial IntermediateField
open scoped IntermediateField

def angle (p : ℕ) (a : ℤ) : ℝ := 2 * Real.pi * a / p
def Admissible (p : ℕ) (a : ℤ) : Prop := 0 < angle p a ∧ angle p a < Real.pi / 2
def cosineAverage (p : ℕ) (a b : ℤ) : ℝ := (Real.cos (angle p a) + Real.cos (angle p b)) / 2
def selectedPoint (p : ℕ) (a b : ℤ) : ℂ :=
  Complex.exp ((Real.arccos (cosineAverage p a b) : ℂ) * Complex.I)
def branchAngle (p : ℕ) (a b : ℤ) : ℝ := Real.arccos (2 * cosineAverage p a b - 1)
def selectedBranch (p : ℕ) (a b : ℤ) : ℂ :=
  Complex.exp (-(branchAngle p a b : ℂ) * Complex.I)
def angleRoot (p : ℕ) (a : ℤ) : ℂ := Complex.exp ((angle p a : ℂ) * Complex.I)

theorem admissible_integer_bounds {p : ℕ} (hp : 0 < p) {a : ℤ} (ha : Admissible p a) :
    0 < a ∧ a < p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hlo := (lt_div_iff₀ hpR).mp ha.1
  have hhi := (div_lt_iff₀ hpR).mp ha.2
  change 0 * (p : ℝ) < 2 * Real.pi * (a : ℝ) at hlo
  change 2 * Real.pi * (a : ℝ) < Real.pi / 2 * (p : ℝ) at hhi
  have haR : (0 : ℝ) < a := by nlinarith [Real.pi_pos]
  have hapR : (a : ℝ) < p := by nlinarith [Real.pi_pos]
  exact ⟨by exact_mod_cast haR, by exact_mod_cast hapR⟩

theorem angleRoot_primitive {p : ℕ} (hp : p.Prime) {a : ℤ} (ha : Admissible p a) :
    IsPrimitiveRoot (angleRoot p a) p := by
  have hab := admissible_integer_bounds hp.pos ha
  have hn : a.natAbs < p := by
    have hh : (a.natAbs : ℤ) < p := by
      rw [Int.natCast_natAbs, abs_of_pos hab.1]
      exact hab.2
    exact_mod_cast hh
  have hz : a.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (ne_of_gt hab.1)
  have hc : IsCoprime a (p : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast]
    exact (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hz) hn)).symm
  convert Complex.isPrimitiveRoot_exp_of_isCoprime a p hp.ne_zero hc using 1
  unfold angleRoot angle
  push_cast
  congr 1
  ring

theorem cosineAverage_bounds {p : ℕ} {a b : ℤ} (ha : Admissible p a) (hb : Admissible p b) :
    0 < cosineAverage p a b ∧ cosineAverage p a b < 1 := by
  have hc {j : ℤ} (hj : Admissible p j) : 0 < Real.cos (angle p j) ∧ Real.cos (angle p j) < 1 := by
    refine ⟨Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hj.1], hj.2⟩, ?_⟩
    simpa using Real.cos_lt_cos_of_nonneg_of_le_pi_div_two (x := 0) (by norm_num) hj.2.le hj.1
  obtain ⟨ha0, ha1⟩ := hc ha
  obtain ⟨hb0, hb1⟩ := hc hb
  unfold cosineAverage
  constructor <;> linarith

theorem exp_angle_add_inv (t : ℝ) :
    Complex.exp ((t : ℂ) * Complex.I) + (Complex.exp ((t : ℂ) * Complex.I))⁻¹ =
      2 * (Real.cos t : ℂ) := by
  rw [← Complex.exp_neg, show -((t : ℂ) * Complex.I) = (-t : ℂ) * Complex.I by ring]
  simp only [Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos]
  ring

theorem selectedBranch_relation {p : ℕ} {a b : ℤ}
    (ha : Admissible p a) (hb : Admissible p b) :
    selectedBranch p a b + (selectedBranch p a b)⁻¹ =
      angleRoot p a + (angleRoot p a)⁻¹ + angleRoot p b + (angleRoot p b)⁻¹ - 2 := by
  have hc := cosineAverage_bounds ha hb
  have ht : Real.cos (branchAngle p a b) = 2 * cosineAverage p a b - 1 :=
    Real.cos_arccos (by linarith) (by linarith)
  have hz := exp_angle_add_inv (-branchAngle p a b)
  have hra := exp_angle_add_inv (angle p a)
  have hrb := exp_angle_add_inv (angle p b)
  simp only [Complex.ofReal_neg, Real.cos_neg, ht] at hz
  change selectedBranch p a b + (selectedBranch p a b)⁻¹ = _ at hz
  change angleRoot p a + (angleRoot p a)⁻¹ = _ at hra
  change angleRoot p b + (angleRoot p b)⁻¹ = _ at hrb
  rw [hz, show angleRoot p a + (angleRoot p a)⁻¹ + angleRoot p b + (angleRoot p b)⁻¹ =
    (angleRoot p a + (angleRoot p a)⁻¹) + (angleRoot p b + (angleRoot p b)⁻¹) by ring,
    hra, hrb]
  unfold cosineAverage
  push_cast
  ring

theorem selectedBranch_algebraic {p : ℕ} (hp : p.Prime) {a b : ℤ}
    (ha : Admissible p a) (hb : Admissible p b) :
    IsAlgebraic ℚ (selectedBranch p a b) := by
  have hr : IsIntegral ℚ (angleRoot p a) := ((angleRoot_primitive hp ha).isIntegral hp.pos).tower_top
  have hs : IsIntegral ℚ (angleRoot p b) := ((angleRoot_primitive hp hb).isIntegral hp.pos).tower_top
  have hw : IsAlgebraic ℚ (angleRoot p a + (angleRoot p a)⁻¹ +
      angleRoot p b + (angleRoot p b)⁻¹ - 2) :=
    (((hr.isAlgebraic.add hr.isAlgebraic.inv).add hs.isAlgebraic).add hs.isAlgebraic.inv).sub
      (by exact isAlgebraic_iff_isIntegral.mpr (isIntegral_natCast (a := 2)))
  exact algebraic_of_add_inv (Complex.exp_ne_zero _) hw (selectedBranch_relation ha hb)

theorem selectedBranch_not_isOfFinOrder {p : ℕ} (hp : p.Prime) {a b : ℤ}
    (ha : Admissible p a) (hb : Admissible p b) :
    ¬ IsOfFinOrder (selectedBranch p a b) := by
  let r : AlgebraicComplex := ⟨angleRoot p a,
    mem_algebraicClosure_iff'.mpr (((angleRoot_primitive hp ha).isIntegral hp.pos).tower_top)⟩
  let s : AlgebraicComplex := ⟨angleRoot p b,
    mem_algebraicClosure_iff'.mpr (((angleRoot_primitive hp hb).isIntegral hp.pos).tower_top)⟩
  let z : AlgebraicComplex := ⟨selectedBranch p a b,
    mem_algebraicClosure_iff.mpr (selectedBranch_algebraic hp ha hb)⟩
  have hr : IsPrimitiveRoot r p := by
    rw [← IsPrimitiveRoot.coe_submonoidClass_iff]
    exact angleRoot_primitive hp ha
  have hs : IsPrimitiveRoot s p := by
    rw [← IsPrimitiveRoot.coe_submonoidClass_iff]
    exact angleRoot_primitive hp hb
  have hrel : z + z⁻¹ = r + r⁻¹ + s + s⁻¹ - 2 := by
    apply Subtype.ext
    exact selectedBranch_relation ha hb
  intro hz
  apply branch_trace_obstruction hp hr hs hrel
  obtain ⟨N, hN, hzN⟩ := isOfFinOrder_iff_pow_eq_one.mp hz
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨N, hN, Subtype.ext hzN⟩

theorem selectedBranch_unit_lower {p : ℕ} {a b : ℤ}
    (ha : Admissible p a) (hb : Admissible p b) :
    ‖selectedBranch p a b‖ = 1 ∧ (selectedBranch p a b).im < 0 := by
  have hc := cosineAverage_bounds ha hb
  have ht0 : 0 < branchAngle p a b := Real.arccos_pos.mpr (by linarith)
  have htπ : branchAngle p a b < Real.pi := Real.arccos_lt_pi.mpr (by linarith)
  constructor
  · simpa [selectedBranch] using Complex.norm_exp_ofReal_mul_I (-branchAngle p a b)
  · rw [selectedBranch, ← Complex.ofReal_neg, Complex.exp_ofReal_mul_I_im, Real.sin_neg]
    exact neg_neg_of_pos (Real.sin_pos_of_pos_of_lt_pi ht0 htπ)

/-- Source-facing selected-point version of lem:resultant. The same A works
for every positive N; algebraicity and nonresonance are conclusions above. -/
theorem selected_exponential_separation {p : ℕ} (hp : p.Prime) {a b : ℤ}
    (ha : Admissible p a) (hb : Admissible p b) :
    ∃ A : ℝ, 0 < A ∧ ∀ N : ℕ, 1 ≤ N →
      Real.exp (-A * N) ≤ ‖1 - selectedBranch p a b ^ N‖ :=
  IsingBulk.Separation.exponential_separation_of_not_isOfFinOrder
    (selectedBranch_algebraic hp ha hb) (selectedBranch_not_isOfFinOrder hp ha hb)

end
end IsingBulk.PrimeFamily
