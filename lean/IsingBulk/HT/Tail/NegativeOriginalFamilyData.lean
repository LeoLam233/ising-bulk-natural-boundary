import IsingBulk.HT.First.NegativeReflectedBranch

/-! Canonical aliases to the actual original negative-family reflected chart.
Geometry and arithmetic are proved in First.NegativeReflectedBranch. -/
namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch

abbrev negativeOriginalReflectedData {p : ℕ} {a b : ℤ}
    (ha : IsingBulk.HT.First.NegativeAdmissible p a)
    (hb : IsingBulk.HT.First.NegativeAdmissible p b) : LocalBranchData :=
  IsingBulk.HT.First.negativeReflectedLocalBranchData ha hb 1 1 zero_lt_one zero_lt_one

theorem negativeOriginalReflectedData_c0_small {p : ℕ} {a b : ℤ}
    (ha : IsingBulk.HT.First.NegativeAdmissible p a)
    (hb : IsingBulk.HT.First.NegativeAdmissible p b) :
    (negativeOriginalReflectedData ha hb).c₀ <
      Real.sin (negativeOriginalReflectedData ha hb).theta/2 :=
  IsingBulk.HT.First.negativeReflectedLocalBranchData_c0_small ha hb 1 1 zero_lt_one zero_lt_one

theorem negativeOriginalReflectedData_theta {p : ℕ} {a b : ℤ}
    (ha : IsingBulk.HT.First.NegativeAdmissible p a)
    (hb : IsingBulk.HT.First.NegativeAdmissible p b) :
    Real.pi-(negativeOriginalReflectedData ha hb).theta =
      (IsingBulk.HT.First.negativeSelectedRegularChart ha hb).theta :=
  IsingBulk.HT.First.negativeReflectedLocalBranchData_reflection ha hb 1 1 zero_lt_one zero_lt_one

theorem negativeOriginalReflectedData_source_radius {p : ℕ} {a b : ℤ}
    (ha : IsingBulk.HT.First.NegativeAdmissible p a)
    (hb : IsingBulk.HT.First.NegativeAdmissible p b) (ε : ℝ) :
    (sourceRadialPair (IsingBulk.HT.First.negativeSelectedRegularChart ha hb).theta ε).1 =
      Real.exp (-(negativeOriginalReflectedData ha hb).c₀*ε) :=
  IsingBulk.HT.First.negativeReflectedLocalBranchData_source_radius
    ha hb 1 1 ε zero_lt_one zero_lt_one

theorem negativeOriginalReflectedData_branch {p : ℕ} {a b : ℤ}
    (ha : IsingBulk.HT.First.NegativeAdmissible p a)
    (hb : IsingBulk.HT.First.NegativeAdmissible p b) :
    Complex.exp (-((negativeOriginalReflectedData ha hb).thetaB:ℂ)*Complex.I) =
      -(IsingBulk.HT.First.negativeSelectedBranch p a b)⁻¹ :=
  IsingBulk.HT.First.negativeReflectedLocalBranchData_branch ha hb 1 1 zero_lt_one zero_lt_one

theorem negativeOriginalReflectedData_algebraic {p : ℕ} (hp : p.Prime) {a b : ℤ}
    (ha : IsingBulk.HT.First.NegativeAdmissible p a)
    (hb : IsingBulk.HT.First.NegativeAdmissible p b) :
    IsAlgebraic ℚ (Complex.exp (-((negativeOriginalReflectedData ha hb).thetaB:ℂ)*Complex.I)) :=
  IsingBulk.HT.First.negativeReflectedLocalBranchData_branch_algebraic
    hp ha hb 1 1 zero_lt_one zero_lt_one

theorem negativeOriginalReflectedData_nonresonant {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    {a b : ℤ} (ha : IsingBulk.HT.First.NegativeAdmissible p a)
    (hb : IsingBulk.HT.First.NegativeAdmissible p b) :
    ∀ N : ℕ,1 ≤ N →
      Complex.exp (-((negativeOriginalReflectedData ha hb).thetaB:ℂ)*Complex.I)^N ≠ 1 :=
  IsingBulk.HT.First.negativeReflectedLocalBranchData_branch_pow_ne_one
    hp hp11 ha hb 1 1 zero_lt_one zero_lt_one

end
end IsingBulk.HT.Tail
