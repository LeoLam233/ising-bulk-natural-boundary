import IsingBulk.HT.First.RegularChartData
import IsingBulk.Analysis.BranchData
import IsingBulk.First.ComplementRadialCompact

/-! Reflected acute branch data for the actual negative integer-angle family.
The reflected lower branch is minus the inverse of the proved negative branch;
no identification with the positive prime family is used. -/
namespace IsingBulk.HT.First
noncomputable section
open IsingBulk.Branch IsingBulk.First IsingBulk.PrimeFamily

/-- The acute source used by the signed negative-family contour construction. -/
def negativeReflectedLocalBranchData {p : ℕ} {a b : ℤ}
    (ha : NegativeAdmissible p a) (hb : NegativeAdmissible p b)
    (τ α : ℝ) (hτ : 0 < τ) (hα : 0 < α) : LocalBranchData where
  theta := Real.pi-Real.arccos (cosineAverage p a b)
  thetaB := Real.pi-Real.arccos (2*cosineAverage p a b+1)
  c₀ := Real.sin (Real.pi-Real.arccos (cosineAverage p a b))/4
  tau := τ
  alpha := α
  theta_pos := by
    have hc := negative_cosineAverage_bounds ha hb
    exact sub_pos.mpr (Real.arccos_lt_pi.mpr hc.1)
  theta_lt := by
    have ht := Real.pi_div_two_lt_arccos.mpr (negative_cosineAverage_bounds ha hb).2
    linarith
  thetaB_pos := by
    have hc := negative_cosineAverage_bounds ha hb
    exact sub_pos.mpr (Real.arccos_lt_pi.mpr (by linarith))
  thetaB_lt := by
    have hc := negative_cosineAverage_bounds ha hb
    have ht : 0 < Real.arccos (2*cosineAverage p a b+1) :=
      Real.arccos_pos.mpr (by linarith)
    linarith
  angle_relation := by
    have hc := negative_cosineAverage_bounds ha hb
    rw [Real.cos_pi_sub, Real.cos_pi_sub,
      Real.cos_arccos (by linarith) (by linarith),
      Real.cos_arccos hc.1.le (by linarith)]
    ring
  c₀_pos := by
    rw [Real.sin_pi_sub]
    exact div_pos (Real.sin_pos_of_pos_of_lt_pi
      (Real.arccos_pos.mpr (by linarith [(negative_cosineAverage_bounds ha hb).2]))
      (Real.arccos_lt_pi.mpr (negative_cosineAverage_bounds ha hb).1)) (by norm_num)
  margin := by
    have hs : 0 < Real.sin (Real.pi-Real.arccos (cosineAverage p a b)) := by
      rw [Real.sin_pi_sub]
      exact Real.sin_pos_of_pos_of_lt_pi
        (Real.arccos_pos.mpr (by linarith [(negative_cosineAverage_bounds ha hb).2]))
        (Real.arccos_lt_pi.mpr (negative_cosineAverage_bounds ha hb).1)
    have hm := mul_le_mul_of_nonneg_left
      (Real.sin_le_one (Real.pi-Real.arccos (2*cosineAverage p a b+1))) hs.le
    nlinarith
  tau_pos := hτ
  alpha_pos := hα

@[simp] theorem negativeReflectedLocalBranchData_theta {p : ℕ} {a b : ℤ}
    (ha : NegativeAdmissible p a) (hb : NegativeAdmissible p b)
    (τ α : ℝ) (hτ : 0 < τ) (hα : 0 < α) :
    (negativeReflectedLocalBranchData ha hb τ α hτ hα).theta =
      Real.pi-(negativeSelectedRegularChart ha hb).theta := rfl

/-- The signed negative tail is evaluated at precisely the original selected angle. -/
theorem negativeReflectedLocalBranchData_reflection {p : ℕ} {a b : ℤ}
    (ha : NegativeAdmissible p a) (hb : NegativeAdmissible p b)
    (τ α : ℝ) (hτ : 0 < τ) (hα : 0 < α) :
    Real.pi-(negativeReflectedLocalBranchData ha hb τ α hτ hα).theta =
      (negativeSelectedRegularChart ha hb).theta := by
  rw [negativeReflectedLocalBranchData_theta]
  ring

@[simp] theorem negativeReflectedLocalBranchData_sin_theta {p : ℕ} {a b : ℤ}
    (ha : NegativeAdmissible p a) (hb : NegativeAdmissible p b)
    (τ α : ℝ) (hτ : 0 < τ) (hα : 0 < α) :
    Real.sin (negativeReflectedLocalBranchData ha hb τ α hτ hα).theta =
      Real.sin (negativeSelectedRegularChart ha hb).theta :=
  Real.sin_pi_sub _

theorem negativeReflectedLocalBranchData_c0_small {p : ℕ} {a b : ℤ}
    (ha : NegativeAdmissible p a) (hb : NegativeAdmissible p b)
    (τ α : ℝ) (hτ : 0 < τ) (hα : 0 < α) :
    (negativeReflectedLocalBranchData ha hb τ α hτ hα).c₀ <
      Real.sin (negativeReflectedLocalBranchData ha hb τ α hτ hα).theta/2 := by
  have hd := (negativeReflectedLocalBranchData ha hb τ α hτ hα).c₀_pos
  change Real.sin (Real.pi-Real.arccos (cosineAverage p a b))/4 < _
  change 0 < Real.sin (Real.pi-Real.arccos (cosineAverage p a b))/4 at hd
  change Real.sin (Real.pi-Real.arccos (cosineAverage p a b))/4 <
    Real.sin (Real.pi-Real.arccos (cosineAverage p a b))/2
  linarith

theorem negativeReflectedLocalBranchData_source_radius {p : ℕ} {a b : ℤ}
    (ha : NegativeAdmissible p a) (hb : NegativeAdmissible p b)
    (τ α ε : ℝ) (hτ : 0 < τ) (hα : 0 < α) :
    (sourceRadialPair (negativeSelectedRegularChart ha hb).theta ε).1 =
      Real.exp (-(negativeReflectedLocalBranchData ha hb τ α hτ hα).c₀*ε) := by
  change Real.exp (-(Real.sin (Real.arccos (cosineAverage p a b))/4)*ε) =
    Real.exp (-(Real.sin (Real.pi-Real.arccos (cosineAverage p a b))/4)*ε)
  rw [Real.sin_pi_sub]

theorem negativeReflectedLocalBranchData_branch {p : ℕ} {a b : ℤ}
    (ha : NegativeAdmissible p a) (hb : NegativeAdmissible p b)
    (τ α : ℝ) (hτ : 0 < τ) (hα : 0 < α) :
    Complex.exp (-((negativeReflectedLocalBranchData ha hb τ α hτ hα).thetaB:ℂ)*Complex.I) =
      -(negativeSelectedBranch p a b)⁻¹ := by
  change Complex.exp (-((Real.pi-Real.arccos (2*cosineAverage p a b+1):ℝ):ℂ)*Complex.I) = _
  have he : -((Real.pi-Real.arccos (2*cosineAverage p a b+1):ℝ):ℂ)*Complex.I =
      -((Real.pi:ℂ)*Complex.I)+(Real.arccos (2*cosineAverage p a b+1):ℂ)*Complex.I := by
    push_cast
    ring
  rw [he, Complex.exp_add, Complex.exp_neg_pi_mul_I, neg_one_mul,
    negativeSelectedBranch, ← Complex.exp_neg]
  congr 2
  ring

theorem negativeReflectedLocalBranchData_branch_algebraic {p : ℕ} (hp : p.Prime)
    {a b : ℤ} (ha : NegativeAdmissible p a) (hb : NegativeAdmissible p b)
    (τ α : ℝ) (hτ : 0 < τ) (hα : 0 < α) :
    IsAlgebraic ℚ
      (Complex.exp (-((negativeReflectedLocalBranchData ha hb τ α hτ hα).thetaB:ℂ)*Complex.I)) := by
  rw [negativeReflectedLocalBranchData_branch]
  exact (negativeSelectedBranch_algebraic hp ha hb).inv.neg

theorem negativeReflectedLocalBranchData_branch_not_isOfFinOrder {p : ℕ}
    (hp : p.Prime) (hp11 : 11 ≤ p) {a b : ℤ}
    (ha : NegativeAdmissible p a) (hb : NegativeAdmissible p b)
    (τ α : ℝ) (hτ : 0 < τ) (hα : 0 < α) :
    ¬ IsOfFinOrder
      (Complex.exp (-((negativeReflectedLocalBranchData ha hb τ α hτ hα).thetaB:ℂ)*Complex.I)) := by
  rw [negativeReflectedLocalBranchData_branch]
  intro hz
  obtain ⟨N,hN,hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hz
  have hinv : IsOfFinOrder ((-(negativeSelectedBranch p a b)⁻¹)⁻¹) :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨N,hN,by rw [inv_pow,hpow,inv_one]⟩
  have hminus : IsOfFinOrder (-1:ℂ) :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨2,by norm_num,by norm_num⟩
  apply negativeSelectedBranch_not_isOfFinOrder hp hp11 ha hb
  simpa only [neg_inv,inv_inv,neg_mul,one_mul,neg_neg] using hminus.mul hinv

theorem negativeReflectedLocalBranchData_branch_pow_ne_one {p : ℕ}
    (hp : p.Prime) (hp11 : 11 ≤ p) {a b : ℤ}
    (ha : NegativeAdmissible p a) (hb : NegativeAdmissible p b)
    (τ α : ℝ) (hτ : 0 < τ) (hα : 0 < α) (N : ℕ) (hN : 1 ≤ N) :
    Complex.exp (-((negativeReflectedLocalBranchData ha hb τ α hτ hα).thetaB:ℂ)*Complex.I)^N ≠ 1 := by
  intro he
  exact negativeReflectedLocalBranchData_branch_not_isOfFinOrder hp hp11 ha hb τ α hτ hα
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨N,by omega,he⟩)

end
end IsingBulk.HT.First
