import IsingBulk.Anisotropic.NegativeDominance.PhysicalConcavity
import IsingBulk.Anisotropic.NegativeDominance.ModelIntegerSelection

/-! Actual analytic scalar branches imply balanced integer Taylor orders.
No crossing, model-dominance, or order-selection premise is assumed. -/
namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open Filter
open scoped Topology

theorem physical_model_integer_selection
    (B rootB : ℂ → ℂ) (phi : ℝ) (hB : AnalyticAt ℂ B 0) (hB0 : B 0 ≠ 0)
    (hroot : ContinuousAt rootB 0) (hroot0 : rootB 0 ≠ 0)
    (hsq : ∀ᶠ t in 𝓝 (0 : ℂ), rootB t^2 = B t) (hphi : Real.sin phi ≠ 0)
    (p : ℕ) (hp : 0 < p) :
    ∃ N : ℕ, ∀ n ≥ N, Odd n → ∃ j : ℕ,
      lowerCrossingOrder n-1 < (j : ℝ) ∧ (j : ℝ) ≤ upperCrossingOrder n ∧
      alpha (n+2*p) < j ∧
      |Real.log ‖physicalModel B rootB phi (n+2*p) j‖-
        Real.log ‖physicalModel B rootB phi n j‖| ≤ 8*(p : ℝ)/(n : ℝ) := by
  obtain ⟨C, hC, he⟩ := physical_modelAnalyticError_eventually_bounded B phi hB hB0
  have hb := tau_complex_tendsto_zero.eventually (hB.continuousAt.eventually_ne hB0)
  have hr := tau_complex_tendsto_zero.eventually (hroot.eventually_ne hroot0)
  have hh := hessianFactor_eventually_nonzero B phi hB
  have hsqn := tau_complex_tendsto_zero.eventually hsq
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hb.and (hr.and (hh.and (hsqn.and he))))
  have hscale := eventually_crossing_scale
    (max 64 (2*(2*|modelQuadraticConstant (B 0) (Real.sin phi)|+14+2*C)+2))
    (max N (max 2 (2*p)))
  have hpi : ∀ᶠ n : ℕ in atTop, Real.pi^2 ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (Real.pi^2))
  obtain ⟨N', hN'⟩ := eventually_atTop.mp (hscale.and hpi)
  refine ⟨N', ?_⟩
  intro n hn ho
  have hsc := (hN' n hn).1
  have hpi' := (hN' n hn).2
  have hnN : N ≤ n := (le_max_left _ _).trans hsc.1
  have hn2 : 2 ≤ n := (le_max_left 2 (2*p)).trans ((le_max_right N _).trans hsc.1)
  have hnp : 2*p ≤ n := (le_max_right 2 (2*p)).trans ((le_max_right N _).trans hsc.1)
  have hsel := exists_integer_model_balance
    (fun k => B (tau k)) (fun k => rootB (tau k))
    (fun k => hessianFactor (B (tau k)) (Real.cos phi) (Real.sin phi) k)
    (B 0) (Real.sin phi) C n p hn2 hp hnp hpi' ho hC.le hphi hsc.2.1 hsc.2.2
    (fun k hk _ => by
      have ht := hN k (hnN.trans hk)
      exact ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1⟩)
    (fun k hk hok => (hN k (hnN.trans hk)).2.2.2.2 hok)
  simpa only [physicalModel] using hsel

end
end IsingBulk.Anisotropic.NegativeDominance
