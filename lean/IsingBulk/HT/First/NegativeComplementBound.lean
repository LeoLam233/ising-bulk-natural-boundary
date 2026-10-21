import IsingBulk.HT.First.NegativeComplementGeometry
import IsingBulk.HT.First.OddComplementBound

/-! Actual negative selected complement bound, from its proved separator.
No negative local mean asymptotic is asserted by this theorem. -/
namespace IsingBulk.HT.First
noncomputable section
open Complex Set Filter IsingBulk.First
open scoped Topology ContDiff

/-- Compatibility with the selected first-order complement. -/
theorem negative_selected_complement_global_bound {p : ℕ} {a b : ℤ}
    (hp : p.Prime) (hp11 : 11 ≤ p)
    (ha : NegativeAdmissible p a) (hb : NegativeAdmissible p b)
    (θ : ℝ) (hθ : 0 < Real.sin θ)
    (hS : sourceS (Complex.exp ((θ:ℂ)*Complex.I)) =
      ((2*PrimeFamily.cosineAverage p a b:ℝ):ℂ))
    (W : DoubleAngularVector p → ℝ) (hW : ContDiff ℝ ∞ W)
    (hWp : DoubleCoordinatePeriodic W)
    (hgood : ∀ u ∈ tsupport W,
      ¬ oddSelectedBadConfiguration a b (angleTuple 1 u.1) (angleTuple 1 u.2)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
        ‖(deriv^[j] (fun s => localizedDoubleFormFactor p (sourceRadialPair θ ε).1 s W))
          (sourceRadialPair θ ε).2‖ ≤ C := by
  apply source_complement_global_bound hp.pos
    (2*PrimeFamily.cosineAverage p a b) θ hθ hS W hW hWp
  intro u hu
  exact negative_odd_selected_active_separating_functional hp hp11 ha hb
    (fun _ => anglePoint_norm (by norm_num) _)
    (fun _ => anglePoint_norm (by norm_num) _) (hgood u hu)


end
end IsingBulk.HT.First
