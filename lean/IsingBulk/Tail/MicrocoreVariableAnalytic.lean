import IsingBulk.Tail.MicrocoreDensityAllOrder
import IsingBulk.Tail.MicrocoreAmplitudeBound

/-! Source regular-factor analyticity follows from the scalar construction
and the actual Y gap, uniformly before N. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets IsingBulk.Branch
open scoped BigOperators

theorem microcoreVariableFactor_analytic {N : ℕ} (z : ℂ × (Fin N → ℂ))
    (J : ℕ) (C : ℝ) (hC : 1 ≤ C) (hf : MicroFactorBounds z J C)
    (hY : 1-regularYProduct z.1 z.2 ≠ 0) :
    AnalyticAt ℂ microcoreVariableFactor z := by
  have ha := (micro_amplitude_jet_product_budget z J C hC hf).analytic
  have hy : AnalyticAt ℂ (fun t : ℂ × (Fin N → ℂ) => regularYProduct t.1 t.2) z := by
    apply Finset.analyticAt_fun_prod
    intro i _
    have hi := (hf.scalar i (1:Fin 4)).analytic
    have hi' : AnalyticAt ℂ (fun t : ℂ × ℂ => (regularY t.1 t.2)⁻¹) (scalarCoordinate i z) := by
      convert! hi using 1
    have hcomp := AnalyticAt.comp (g := fun t : ℂ × ℂ => (regularY t.1 t.2)⁻¹)
      (f := scalarCoordinate i) hi' ((scalarCoordinate i).analyticAt z)
    have hh := hcomp.inv (inv_ne_zero (regularY_ne_zero z.1 (z.2 i)))
    convert! hh using 1
    ext t
    simp [scalarCoordinate]
  exact ha.div (analyticAt_const.sub hy) hY

theorem microcore_variable_uniform_analytic (s₀ : ℂ) (c : ℝ) (hs : s₀ ≠ 0)
    (hS : s₀+s₀⁻¹=(1+c:ℂ)) (hc : |c|<1) :
    ∃ r : ℝ, 0 < r ∧ ∀ N : ℕ, ∀ s : ℂ, ∀ φ : Fin N → ℂ,
      ‖s-s₀‖ < r → (∀ i, ‖φ i‖ < r) → 1-regularYProduct s φ ≠ 0 →
      AnalyticAt ℂ microcoreVariableFactor (s,φ) := by
  obtain ⟨C,r,hC,hr,hb⟩ := micro_factor_bounds_uniform s₀ c hs hS hc 0
  exact ⟨r,hr,fun N s φ hs' hφ hY => microcoreVariableFactor_analytic (s,φ) 0 C hC
    (hb N s φ hs' hφ) hY⟩

end
end IsingBulk.Tail
