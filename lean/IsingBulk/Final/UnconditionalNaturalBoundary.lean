import IsingBulk.Tail.AbsoluteTailAssembly
import IsingBulk.Final.ConditionalNaturalBoundary
import IsingBulk.Final.ConditionalPhysicalBoundary

/-! Discharge the manuscript's absolute TAIL premise using the internal
sector assembly. The published fixed-order input and the real physical
identification inputs retain exactly their previous scope. -/
namespace IsingBulk.Final
noncomputable section
open IsingBulk.First IsingBulk.Tail

/-- The literal all-order absolute upper tail at every admissible selected
prime point. There is no sector-smallness or tail-smallness hypothesis. -/
theorem theorem_tail {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    {a b : ℤ} (ha : PrimeFamily.Admissible p a)
    (hb : PrimeFamily.Admissible p b) (hab : a ≠ b) :
    ∀ j : ℕ, j ≤ (2*p)^2/2-1 →
      AbsoluteUpperTailSmall p (selectedOrderedChart ha hb).theta j :=
  selected_absolute_upper_tail_small hp hp11 ha hb hab

/-- Complete TAIL package: convergence of the exact higher-even norm sequence
at each positive radial parameter, together with the existing little-o bound. -/
theorem theorem_tail_with_summability {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    {a b : ℤ} (ha : PrimeFamily.Admissible p a)
    (hb : PrimeFamily.Admissible p b) (hab : a ≠ b) :
    ∀ j : ℕ, j ≤ (2*p)^2/2-1 →
      (∀ eps : ℝ, 0 < eps → Summable (fun n : ℕ =>
        ‖iteratedDeriv j (upperFormFactor (2*(n+p+1)))
          (IsingBulk.Branch.radialParameter (selectedOrderedChart ha hb).theta eps)‖)) ∧
      AbsoluteUpperTailSmall p (selectedOrderedChart ha hb).theta j := fun j hj =>
  ⟨fun _ heps => actual_upper_tail_summable p j (selectedOrderedChart ha hb).sin_theta_pos heps,
   theorem_tail hp hp11 ha hb hab j hj⟩

/-- Natural boundary of the internally constructed exterior normalized bulk
series, with the absolute-tail premise discharged. -/
theorem theorem_nb
    (hTW : ∀ p : ℕ, ∀ a b : ℤ, p.Prime → 11 ≤ p →
      PrimeFamily.Admissible p a → PrimeFamily.Admissible p b → a ≠ b →
      PublishedTWFixedOrderInput (PrimeFamily.selectedPoint p a b)) :
    ∀ z : ℂ, ‖z‖ = 1 → ¬ HasExteriorExtension exteriorNormalizedBulk z := by
  exact theorem_conditional hTW
    (fun _ _ _ hp hp11 ha hb hab => theorem_tail hp hp11 ha hb hab)

/-- The physical bulk susceptibility germ and every boundary point retain
the original E1, E2 and fixed-order TW input boundaries. No TAIL input remains. -/
theorem theorem_nb_physical {J : ℝ} (hJ : 0 < J)
    {chi : ℂ → ℂ} {M : ℝ → ℂ}
    (hE1 : PhysicalSusceptibilityE1 J chi M) (hE2 : YangMagnetizationE2 M)
    (hTW : ∀ p : ℕ, ∀ a b : ℤ, p.Prime → 11 ≤ p →
      PrimeFamily.Admissible p a → PrimeFamily.Admissible p b → a ≠ b →
      PublishedTWFixedOrderInput (PrimeFamily.selectedPoint p a b)) :
    AnalyticOnNhd ℂ (rightPhysicalBulk J) {s : ℂ | 1 < ‖s‖ ∧ 0 < s.re} ∧
      (∀ x : ℝ, 16 < x → chi (x:ℂ) = rightPhysicalBulk J (x:ℂ)) ∧
      (∀ z : ℂ, ‖z‖ = 1 → ¬ HasPhysicalBoundaryExtension J exteriorNormalizedBulk z) := by
  exact theorem_conditional_physical hJ hE1 hE2 hTW
    (fun _ _ _ hp hp11 ha hb hab => theorem_tail hp hp11 ha hb hab)

end
end IsingBulk.Final
