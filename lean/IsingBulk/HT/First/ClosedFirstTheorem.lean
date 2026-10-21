import IsingBulk.HT.First.ClosedCoefficientIdentification
import IsingBulk.HT.First.OddFirstTheorem
import IsingBulk.HT.First.NegativeFirstTheorem
import IsingBulk.HT.First.OddSharpFullFirstBounds

/-! The exact manuscript first-coefficient formula attached to the literal
full-site source coefficient C_p=f_p+2T_p, on both selected prime families.
These finite-particle statements do not assert an infinite-tail estimate or
an unconditional physical-susceptibility natural-boundary endpoint. -/
namespace IsingBulk.HT.First
noncomputable section
open Complex Filter IsingBulk.First
open scoped Topology

/-- Positive selected family, with the fully evaluated Hermite amplitude. -/
theorem first_standard_odd_source_closed_asymptotic {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    {a b : ℤ} (ha : PrimeFamily.Admissible p a) (hb : PrimeFamily.Admissible p b)
    (hab : a ≠ b) :
    let k := derivativeOrder p
    let A := selectedOrderedChart ha hb
    let L := closedLeadingCoefficient p A.theta (curvatureNumerator A.alpha A.beta)
    4*L ≠ 0 ∧ Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
      (fun epsilon => (deriv^[k] (standardFormFactor p (sourceRadialPair A.theta epsilon).1))
        (sourceRadialPair A.theta epsilon).2-(epsilon:ℂ)⁻¹*(4*L))
      (fun epsilon => (epsilon:ℂ)⁻¹) := by
  have h := first_standard_odd_source_asymptotic hp hp11 ha hb hab
  dsimp only at h ⊢
  rw [oddLocalLeadingCoefficient_eq_closed _ (hp.odd_of_ne_two (by omega)) (by omega)] at h
  exact h

/-- The closed first coefficient and sharp lower derivatives for the literal
positive-family full-site source, with no asymptotic input hypotheses. -/
theorem first_standard_odd_source_closed_and_sharp {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    {a b : ℤ} (ha : PrimeFamily.Admissible p a) (hb : PrimeFamily.Admissible p b)
    (hab : a ≠ b) :
    let k := derivativeOrder p
    let A := selectedOrderedChart ha hb
    let L := closedLeadingCoefficient p A.theta (curvatureNumerator A.alpha A.beta)
    (4*L ≠ 0 ∧ Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
      (fun epsilon => (deriv^[k] (standardFormFactor p (sourceRadialPair A.theta epsilon).1))
        (sourceRadialPair A.theta epsilon).2-(epsilon:ℂ)⁻¹*(4*L))
      (fun epsilon => (epsilon:ℂ)⁻¹)) ∧
    ∃ e : ℝ, 0 < e ∧
      (∃ C : ℝ, 0 < C ∧ ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ e →
        ‖(deriv^[k-1] (standardFormFactor p (sourceRadialPair A.theta epsilon).1))
          (sourceRadialPair A.theta epsilon).2‖ ≤ C*(1+|Real.log epsilon|)) ∧
      (∀ j : ℕ, j+1 < k → ∃ C : ℝ, 0 < C ∧ ∀ epsilon : ℝ,
        0 < epsilon → epsilon ≤ e →
        ‖(deriv^[j] (standardFormFactor p (sourceRadialPair A.theta epsilon).1))
          (sourceRadialPair A.theta epsilon).2‖ ≤ C) :=
  ⟨first_standard_odd_source_closed_asymptotic hp hp11 ha hb hab,
    first_standard_odd_source_sharp_lower_bounds hp hp11 ha hb hab⟩

namespace Regular

/-- Negative selected family on its original integer-angle point and sheet. -/
theorem negative_first_standard_odd_source_closed_asymptotic {p : ℕ}
    (hp : p.Prime) (hp11 : 11 ≤ p)
    {a b : ℤ} (ha : NegativeAdmissible p a) (hb : NegativeAdmissible p b)
    (hab : a ≠ b) :
    let k := derivativeOrder p
    let A := negativeSelectedRegularChart ha hb
    let L := closedLeadingCoefficient p A.theta (curvatureNumerator A.alpha A.beta)
    4*L ≠ 0 ∧ Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
      (fun epsilon => (deriv^[k] (standardFormFactor p (sourceRadialPair A.theta epsilon).1))
        (sourceRadialPair A.theta epsilon).2-(epsilon:ℂ)⁻¹*(4*L))
      (fun epsilon => (epsilon:ℂ)⁻¹) := by
  have h := negative_first_standard_odd_source_asymptotic hp hp11 ha hb hab
  dsimp only at h ⊢
  rw [oddLocalLeadingCoefficient_eq_closed _ (hp.odd_of_ne_two (by omega)) (by omega)] at h
  exact h

/-- The same closed coefficient and sharp lower jets on the original negative
selected-point family, not on a substituted reflected source. -/
theorem negative_first_standard_odd_source_closed_and_sharp {p : ℕ}
    (hp : p.Prime) (hp11 : 11 ≤ p)
    {a b : ℤ} (ha : NegativeAdmissible p a) (hb : NegativeAdmissible p b)
    (hab : a ≠ b) :
    let k := derivativeOrder p
    let A := negativeSelectedRegularChart ha hb
    let L := closedLeadingCoefficient p A.theta (curvatureNumerator A.alpha A.beta)
    (4*L ≠ 0 ∧ Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
      (fun epsilon => (deriv^[k] (standardFormFactor p (sourceRadialPair A.theta epsilon).1))
        (sourceRadialPair A.theta epsilon).2-(epsilon:ℂ)⁻¹*(4*L))
      (fun epsilon => (epsilon:ℂ)⁻¹)) ∧
    ∃ e : ℝ, 0 < e ∧
      (∃ C : ℝ, 0 < C ∧ ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ e →
        ‖(deriv^[k-1] (standardFormFactor p (sourceRadialPair A.theta epsilon).1))
          (sourceRadialPair A.theta epsilon).2‖ ≤ C*(1+|Real.log epsilon|)) ∧
      (∀ j : ℕ, j+1 < k → ∃ C : ℝ, 0 < C ∧ ∀ epsilon : ℝ,
        0 < epsilon → epsilon ≤ e →
        ‖(deriv^[j] (standardFormFactor p (sourceRadialPair A.theta epsilon).1))
          (sourceRadialPair A.theta epsilon).2‖ ≤ C) :=
  ⟨negative_first_standard_odd_source_closed_asymptotic hp hp11 ha hb hab,
    negative_first_standard_odd_source_sharp_lower_bounds hp hp11 ha hb hab⟩

end Regular
end
end IsingBulk.HT.First
