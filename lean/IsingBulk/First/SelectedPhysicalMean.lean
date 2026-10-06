import IsingBulk.First.PhysicalMeanResidue
import IsingBulk.First.MeanSelectedData

/-! Physical mean endpoint instantiated by the immutable prime-family data. -/
namespace IsingBulk.First
noncomputable section
open Complex IsingBulk.Branch
open scoped BigOperators Topology

theorem selected_physical_mean_residue {p : ℕ} (hp : p.Prime) {a b : ℤ}
    (ha : IsingBulk.PrimeFamily.Admissible p a) (hb : IsingBulk.PrimeFamily.Admissible p b)
    (L : ℝ) (hL : 0 < L) :
    ∃ delta h epsilon₀ c : ℝ, 0 < delta ∧ delta ≤ L ∧ 0 < h ∧ 0 < epsilon₀ ∧ 0 < c ∧
      ∀ eta : ℝ → ℂ, Continuous eta → (∀ x : ℝ, |x| ≤ delta → eta x=1) →
      (∀ x : ℝ, 2*delta < |x| → eta x=0) →
      (∀ (epsilon : ℝ) (t : Fin (2*p-1) → ℝ) (s : ℂ), 0 < epsilon → epsilon < epsilon₀ →
        (∑ i, (shapeExtend t i)^2) < h^2 →
        ‖s-radialParameter (selectedOrderedChart ha hb).theta epsilon‖ < (Real.sin (selectedOrderedChart ha hb).theta/16)*epsilon →
        (∫ v : ℝ, eta v * meanLocalDensity s (-(Real.sin (selectedOrderedChart ha hb).theta/4)*epsilon) (IsingBulk.PrimeFamily.angle p a) t (v:ℂ)) =
          postMeanDensity s (IsingBulk.PrimeFamily.angle p a) t +
            meanRegularError eta s (-(Real.sin (selectedOrderedChart ha hb).theta/4)*epsilon) (IsingBulk.PrimeFamily.angle p a) delta t) ∧
      (∀ j : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (epsilon : ℝ) (t : Fin (2*p-1) → ℝ) (s : ℂ),
        0 < epsilon → epsilon < epsilon₀ → (∑ i, (shapeExtend t i)^2) < h^2 →
        ‖s-radialParameter (selectedOrderedChart ha hb).theta epsilon‖ < (Real.sin (selectedOrderedChart ha hb).theta/16)*epsilon →
        ‖(deriv^[j] (fun z => meanRegularError eta z (-(Real.sin (selectedOrderedChart ha hb).theta/4)*epsilon)
          (IsingBulk.PrimeFamily.angle p a) delta t)) s‖ ≤ C) ∧
      (∀ (epsilon : ℝ) (t : Fin (2*p-1) → ℝ), 0 < epsilon → epsilon < epsilon₀ →
        (∑ i, (shapeExtend t i)^2) < h^2 →
        c*(epsilon+∑ i, (shapeExtend t i)^2) ≤
          ‖shapePoleDenominator (radialParameter (selectedOrderedChart ha hb).theta epsilon) (IsingBulk.PrimeFamily.angle p a) t‖) := by
  have hN : 2*p-1+1 = 2*p := by have := hp.pos; omega
  have hNc : ((2*p-1:ℕ):ℂ)+1 = ((2*p:ℕ):ℂ) := by exact_mod_cast hN
  have hAlpha : exp (-(((2*p-1:ℕ):ℂ)+1)*((selectedOrderedChart ha hb).alpha:ℂ)*I)=1 := by
    rw [hNc]
    exact selected_lower_center_root hp ha
  have hBeta : exp (-(((2*p-1:ℕ):ℂ)+1)*((selectedOrderedChart ha hb).beta:ℂ)*I)=1 := by
    rw [hNc]
    exact selected_lower_center_root hp hb
  exact physical_mean_residue (selectedOrderedChart ha hb) (2*p-1) hAlpha hBeta L hL

end
end IsingBulk.First
