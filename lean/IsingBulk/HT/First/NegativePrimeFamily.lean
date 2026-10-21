import IsingBulk.Algebra.NickelOrder
import IsingBulk.HT.First.NegativeTrace

/-! The actual negative-cosine prime family and its exceptional −1 branch.
The root is the physical lower root at S+1, with nonresonance proved by the
new second-moment trace obstruction. No positive-family sign inference is used. -/
namespace IsingBulk.HT.First
noncomputable section
open IsingBulk.PrimeFamily Polynomial IntermediateField
open scoped IntermediateField

/-- The manuscript's second angular interval, using the same integer angles. -/
def NegativeAdmissible (p : ℕ) (a : ℤ) : Prop :=
  Real.pi/2 < angle p a ∧ angle p a < Real.pi

theorem negative_admissible_integer_bounds {p : ℕ} (hp : 0 < p) {a : ℤ}
    (ha : NegativeAdmissible p a) : 0 < a ∧ a < p := by
  have hpR : (0:ℝ)<p := by exact_mod_cast hp
  have hlo := (lt_div_iff₀ hpR).mp ha.1
  have hhi := (div_lt_iff₀ hpR).mp ha.2
  change Real.pi/2*(p:ℝ) < 2*Real.pi*(a:ℝ) at hlo
  change 2*Real.pi*(a:ℝ) < Real.pi*(p:ℝ) at hhi
  have haR : (0:ℝ)<a := by nlinarith [Real.pi_pos]
  have hapR : (a:ℝ)<p := by nlinarith [Real.pi_pos]
  exact ⟨by exact_mod_cast haR,by exact_mod_cast hapR⟩

theorem negative_angleRoot_primitive {p : ℕ} (hp : p.Prime) {a : ℤ}
    (ha : NegativeAdmissible p a) : IsPrimitiveRoot (angleRoot p a) p := by
  have hab := negative_admissible_integer_bounds hp.pos ha
  have hn : a.natAbs < p := by
    have hh : (a.natAbs:ℤ)<p := by
      rw [Int.natCast_natAbs,abs_of_pos hab.1]
      exact hab.2
    exact_mod_cast hh
  have hz : a.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (ne_of_gt hab.1)
  have hc : IsCoprime a (p:ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime,Int.natAbs_natCast]
    exact (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hz) hn)).symm
  convert Complex.isPrimitiveRoot_exp_of_isCoprime a p hp.ne_zero hc using 1
  unfold angleRoot angle
  push_cast
  congr 1
  ring

theorem negative_cosineAverage_bounds {p : ℕ} {a b : ℤ}
    (ha : NegativeAdmissible p a) (hb : NegativeAdmissible p b) :
    -1 < cosineAverage p a b ∧ cosineAverage p a b < 0 := by
  have hc {j : ℤ} (hj : NegativeAdmissible p j) :
      -1 < Real.cos (angle p j) ∧ Real.cos (angle p j) < 0 := by
    constructor
    · have h := Real.cos_lt_cos_of_nonneg_of_le_pi
        (by linarith [Real.pi_pos,hj.1] : 0 ≤ angle p j) (le_refl Real.pi) hj.2
      simpa only [Real.cos_pi] using h
    · exact Real.cos_neg_of_pi_div_two_lt_of_lt hj.1 (by linarith [Real.pi_pos,hj.2])
  obtain ⟨ha0,ha1⟩ := hc ha
  obtain ⟨hb0,hb1⟩ := hc hb
  unfold cosineAverage
  constructor <;> linarith

theorem negative_selectedPoint_relation {p : ℕ} {a b : ℤ}
    (ha : NegativeAdmissible p a) (hb : NegativeAdmissible p b) :
    selectedPoint p a b+(selectedPoint p a b)⁻¹ = 2*(cosineAverage p a b:ℂ) := by
  have hc := negative_cosineAverage_bounds ha hb
  simpa only [selectedPoint,Real.cos_arccos hc.1.le (by linarith : cosineAverage p a b ≤ 1)]
    using exp_angle_add_inv (Real.arccos (cosineAverage p a b))

/-- Second-moment trace excludes the rational candidate left open by the
negative first moment. -/
theorem negative_cosineAverage_not_rational {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    {a b : ℤ} (ha : NegativeAdmissible p a) (hb : NegativeAdmissible p b) (q : ℚ) :
    (cosineAverage p a b:ℂ) ≠ (q:ℂ) := by
  intro hq
  let r : AlgebraicComplex := ⟨angleRoot p a,
    mem_algebraicClosure_iff'.mpr (((negative_angleRoot_primitive hp ha).isIntegral hp.pos).tower_top)⟩
  let s : AlgebraicComplex := ⟨angleRoot p b,
    mem_algebraicClosure_iff'.mpr (((negative_angleRoot_primitive hp hb).isIntegral hp.pos).tower_top)⟩
  have hr : IsPrimitiveRoot r p := by
    rw [← IsPrimitiveRoot.coe_submonoidClass_iff]
    exact negative_angleRoot_primitive hp ha
  have hs : IsPrimitiveRoot s p := by
    rw [← IsPrimitiveRoot.coe_submonoidClass_iff]
    exact negative_angleRoot_primitive hp hb
  apply primitive_sum_not_rational hp hp11 hr hs (4*q)
  apply Subtype.ext
  change angleRoot p a+(angleRoot p a)⁻¹+angleRoot p b+(angleRoot p b)⁻¹ = ((4*q:ℚ):ℂ)
  have hra := exp_angle_add_inv (angle p a)
  have hrb := exp_angle_add_inv (angle p b)
  change angleRoot p a+(angleRoot p a)⁻¹ = _ at hra
  change angleRoot p b+(angleRoot p b)⁻¹ = _ at hrb
  calc
    _ = 4*(cosineAverage p a b:ℂ) := by
      unfold cosineAverage
      simp only [Complex.ofReal_div,Complex.ofReal_add,Complex.ofReal_ofNat]
      linear_combination hra+hrb
    _ = _ := by rw [hq]; push_cast; ring

/-- Physical lower branch at the exceptional other-coordinate value −1. -/
def negativeSelectedBranch (p : ℕ) (a b : ℤ) : ℂ :=
  Complex.exp (-(Real.arccos (2*cosineAverage p a b+1):ℂ)*Complex.I)

theorem negativeSelectedBranch_relation {p : ℕ} {a b : ℤ}
    (ha : NegativeAdmissible p a) (hb : NegativeAdmissible p b) :
    negativeSelectedBranch p a b+(negativeSelectedBranch p a b)⁻¹ =
      angleRoot p a+(angleRoot p a)⁻¹+angleRoot p b+(angleRoot p b)⁻¹+2 := by
  have hc := negative_cosineAverage_bounds ha hb
  have ht : Real.cos (Real.arccos (2*cosineAverage p a b+1)) = 2*cosineAverage p a b+1 :=
    Real.cos_arccos (by linarith) (by linarith)
  have hz := exp_angle_add_inv (-Real.arccos (2*cosineAverage p a b+1))
  have hra := exp_angle_add_inv (angle p a)
  have hrb := exp_angle_add_inv (angle p b)
  simp only [Complex.ofReal_neg,Real.cos_neg,ht] at hz
  change negativeSelectedBranch p a b+(negativeSelectedBranch p a b)⁻¹ = _ at hz
  change angleRoot p a+(angleRoot p a)⁻¹ = _ at hra
  change angleRoot p b+(angleRoot p b)⁻¹ = _ at hrb
  rw [hz]
  unfold cosineAverage
  simp only [Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_one]
  linear_combination -hra-hrb

theorem negativeSelectedBranch_algebraic {p : ℕ} (hp : p.Prime) {a b : ℤ}
    (ha : NegativeAdmissible p a) (hb : NegativeAdmissible p b) :
    IsAlgebraic ℚ (negativeSelectedBranch p a b) := by
  have hr : IsIntegral ℚ (angleRoot p a) := ((negative_angleRoot_primitive hp ha).isIntegral hp.pos).tower_top
  have hs : IsIntegral ℚ (angleRoot p b) := ((negative_angleRoot_primitive hp hb).isIntegral hp.pos).tower_top
  have hw : IsAlgebraic ℚ (angleRoot p a+(angleRoot p a)⁻¹+angleRoot p b+(angleRoot p b)⁻¹+2) :=
    (((hr.isAlgebraic.add hr.isAlgebraic.inv).add hs.isAlgebraic).add hs.isAlgebraic.inv).add
      (by exact isAlgebraic_iff_isIntegral.mpr (isIntegral_natCast (a := 2)))
  exact algebraic_of_add_inv (Complex.exp_ne_zero _) hw (negativeSelectedBranch_relation ha hb)

theorem negativeSelectedBranch_not_isOfFinOrder {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    {a b : ℤ} (ha : NegativeAdmissible p a) (hb : NegativeAdmissible p b) :
    ¬ IsOfFinOrder (negativeSelectedBranch p a b) := by
  let r : AlgebraicComplex := ⟨angleRoot p a,
    mem_algebraicClosure_iff'.mpr (((negative_angleRoot_primitive hp ha).isIntegral hp.pos).tower_top)⟩
  let s : AlgebraicComplex := ⟨angleRoot p b,
    mem_algebraicClosure_iff'.mpr (((negative_angleRoot_primitive hp hb).isIntegral hp.pos).tower_top)⟩
  let z : AlgebraicComplex := ⟨negativeSelectedBranch p a b,
    mem_algebraicClosure_iff.mpr (negativeSelectedBranch_algebraic hp ha hb)⟩
  have hr : IsPrimitiveRoot r p := by
    rw [← IsPrimitiveRoot.coe_submonoidClass_iff]
    exact negative_angleRoot_primitive hp ha
  have hs : IsPrimitiveRoot s p := by
    rw [← IsPrimitiveRoot.coe_submonoidClass_iff]
    exact negative_angleRoot_primitive hp hb
  have hrel : z+z⁻¹=r+r⁻¹+s+s⁻¹+2 := by
    apply Subtype.ext
    exact negativeSelectedBranch_relation ha hb
  intro hz
  apply negative_branch_trace_obstruction hp hp11 hr hs hrel
  obtain ⟨N,hN,hzN⟩ := isOfFinOrder_iff_pow_eq_one.mp hz
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨N,hN,Subtype.ext hzN⟩

theorem negativeSelectedBranch_unit_lower {p : ℕ} {a b : ℤ}
    (ha : NegativeAdmissible p a) (hb : NegativeAdmissible p b) :
    ‖negativeSelectedBranch p a b‖=1 ∧ (negativeSelectedBranch p a b).im<0 := by
  have hc := negative_cosineAverage_bounds ha hb
  have ht0 : 0 < Real.arccos (2*cosineAverage p a b+1) := Real.arccos_pos.mpr (by linarith)
  have htpi : Real.arccos (2*cosineAverage p a b+1) < Real.pi := Real.arccos_lt_pi.mpr (by linarith)
  constructor
  · simpa [negativeSelectedBranch] using
      Complex.norm_exp_ofReal_mul_I (-Real.arccos (2*cosineAverage p a b+1))
  · rw [negativeSelectedBranch,← Complex.ofReal_neg,Complex.exp_ofReal_mul_I_im,Real.sin_neg]
    exact neg_neg_of_pos (Real.sin_pos_of_pos_of_lt_pi ht0 htpi)

theorem negative_selected_exponential_separation {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    {a b : ℤ} (ha : NegativeAdmissible p a) (hb : NegativeAdmissible p b) :
    ∃ A : ℝ,0<A ∧ ∀ N : ℕ,1≤N →
      Real.exp (-A*N) ≤ ‖1-negativeSelectedBranch p a b^N‖ :=
  IsingBulk.Separation.exponential_separation_of_not_isOfFinOrder
    (negativeSelectedBranch_algebraic hp ha hb) (negativeSelectedBranch_not_isOfFinOrder hp hp11 ha hb)

end
end IsingBulk.HT.First
