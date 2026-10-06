import IsingBulk.First.CompatibleMeanSource
import IsingBulk.First.ShapeCutoffLift

/-! The constructed free-coordinate cutoff is attached to the actual local
mean-asymptotic observable, with the identical intrinsic lift and one factorial. -/
namespace IsingBulk.First
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace CompatibleYCutoffData
variable {n : ℕ} {alpha beta : ℝ} {U : Set (Fin n → ℝ)}

theorem source_localizedSmoothMeanIntegral (c : CompatibleYCutoffData n alpha beta U)
    (a : OrderedChartData) (s : ℂ) (rho : ℝ) (hr1 : Real.exp rho < 1)
    (hm : (Real.exp rho)⁻¹-Real.exp rho < (sourceS s).im) :
    weightedReducedFormFactor (n+1) (Real.exp rho) (globalRoot s)
      (fixedYChartWeight a.alpha c.chi c.eta) =
      localizedSmoothMeanIntegral a (liftShapeCutoff c.chi) (fun v => (c.eta v:ℂ)) rho c.delta s := by
  rw [c.source_mean_integral a.alpha s rho hr1 hm]
  unfold localizedSmoothMeanIntegral
  simp only [liftShapeCutoff_apply_chart]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => by dsimp only; ring)

/-- The exact source derivative is the derivative in the actual local leading
asymptotic theorem; no cutoff substitution or duplicate N! is left to assembly. -/
theorem source_localizedSmoothMean_derivative (c : CompatibleYCutoffData n alpha beta U)
    (a : OrderedChartData) (s : ℂ) (rho : ℝ) (hr1 : Real.exp rho < 1)
    (hm : (Real.exp rho)⁻¹-Real.exp rho < (sourceS s).im) (j : ℕ) :
    iteratedDeriv j (fun z => weightedReducedFormFactor (n+1) (Real.exp rho) (globalRoot z)
      (fixedYChartWeight a.alpha c.chi c.eta)) s =
      (deriv^[j] (localizedSmoothMeanIntegral a (liftShapeCutoff c.chi)
        (fun v => (c.eta v:ℂ)) rho c.delta)) s := by
  have he : (fun z => weightedReducedFormFactor (n+1) (Real.exp rho) (globalRoot z)
      (fixedYChartWeight a.alpha c.chi c.eta)) =ᶠ[𝓝 s]
      localizedSmoothMeanIntegral a (liftShapeCutoff c.chi) (fun v => (c.eta v:ℂ)) rho c.delta := by
    filter_upwards [dampingDomain_mem_nhds (dampingDomain_of_margin (Real.exp_pos rho) hr1 hm)] with z hz
    exact c.source_localizedSmoothMeanIntegral a z rho hr1 hz.2
  simpa only [iteratedDeriv_eq_iterate] using he.iteratedDeriv_eq j

end CompatibleYCutoffData
end
end IsingBulk.First
