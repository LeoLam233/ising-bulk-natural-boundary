import IsingBulk.Final.PhysicalBoundaryExtension

/-! Complete physical-germ form of the source conditional criterion.
The actual normalized exterior series is internal, and chi=beta*X is
identified by real-only E1/E2. All local inverse sheets are covered. -/
namespace IsingBulk.Final
noncomputable section
open Set IsingBulk.First IsingBulk.Tail

theorem theorem_conditional_physical {J : ℝ} (hJ : 0 < J)
    {chi : ℂ → ℂ} {M : ℝ → ℂ}
    (hE1 : PhysicalSusceptibilityE1 J chi M) (hE2 : YangMagnetizationE2 M)
    (hTW : ∀ p : ℕ, ∀ a b : ℤ, p.Prime → 11 ≤ p →
      PrimeFamily.Admissible p a → PrimeFamily.Admissible p b → a ≠ b →
      PublishedTWFixedOrderInput (PrimeFamily.selectedPoint p a b))
    (hTail : ∀ p : ℕ, ∀ a b : ℤ, ∀ _hp : p.Prime, ∀ _hp11 : 11 ≤ p,
      ∀ ha : PrimeFamily.Admissible p a, ∀ hb : PrimeFamily.Admissible p b,
      a ≠ b → ∀ j : ℕ, j ≤ (2*p)^2/2-1 →
      AbsoluteUpperTailSmall p (selectedOrderedChart ha hb).theta j) :
    AnalyticOnNhd ℂ (rightPhysicalBulk J) {s : ℂ | 1 < ‖s‖ ∧ 0 < s.re} ∧
      (∀ x : ℝ, 16 < x → chi (x:ℂ)=rightPhysicalBulk J (x:ℂ)) ∧
      (∀ z : ℂ, ‖z‖=1 → ¬ HasPhysicalBoundaryExtension J exteriorNormalizedBulk z) := by
  obtain ⟨ha,hreal⟩ := physical_real_germ_identification hJ hE1 hE2
  exact ⟨ha,hreal,physical_no_boundary_extension exteriorNormalizedBulk_analyticOn
    (theorem_conditional hTW hTail) hJ⟩

end
end IsingBulk.Final
