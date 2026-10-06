import IsingBulk.First.SourceAuxiliaryInterchange

/-! Actual-source instantiation of the generated full-phase parameter jets,
now connected to the genuine noncompact differentiation theorem. -/
namespace IsingBulk.First
noncomputable section
open Set MeasureTheory
open scoped BigOperators

theorem sourceAuxiliaryDensity_jet_eq (N : ℕ) (hN : 0 < N) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (w : DoubleAngularVector N → ℝ)
    (J : Finset (SingularFactorIndex N)) (u : DoubleAngularVector N) (ξ : J → ℝ)
    {s : ℂ} (hm : r⁻¹-r < (sourceS s).im) (j : ℕ) :
    iteratedDeriv j (fun t => sourceAuxiliaryDensity r w J t (u,ξ)) s =
      parameterExpPolynomial (dispersionAuxiliaryTotal (fun f : J => f.1) ξ : ℂ)
        (parameterExpTerms (fun t => localizedRegularAmplitude r t w J u) sourceTemperaturePhase j) s *
        Complex.exp (sourcePhaseSum r s (fun _ => 1) (fun _ => 1) (fun f : J => f.1) ξ u) := by
  simpa only [iteratedDeriv_eq_iterate, sourceAuxiliaryDensity] using
    source_full_phase_derivative r w J u ξ (dampingDomain r) (dampingDomain_isOpen r)
      (fun _ ht => ht.1)
      (fun _ ht f _ => sourceFactorDenominator_ne_zero_damped N hN hr hr1 ht u f)
      j (dampingDomain_of_margin hr hr1 hm)

end
end IsingBulk.First
