import IsingBulk.First.MeanSourceIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! The constructed fixed compatible y cutoff is attached to the actual mean
integral at the same delta, preserving all source variables and normalizations. -/
namespace IsingBulk.First
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace CompatibleYCutoffData
variable {n : ℕ} {alpha beta : ℝ} {U : Set (Fin n → ℝ)}

theorem source_mean_integral (c : CompatibleYCutoffData n alpha beta U)
    (gamma : ℝ) (s : ℂ) (rho : ℝ) (hr1 : Real.exp rho < 1)
    (hm : (Real.exp rho)⁻¹-Real.exp rho < (sourceS s).im) :
    weightedReducedFormFactor (n+1) (Real.exp rho) (globalRoot s)
      (fixedYChartWeight gamma c.chi c.eta) =
      ((n+1).factorial:ℂ)⁻¹ * ∫ t : Fin n → ℝ, (c.chi t:ℂ)*
        smoothMeanIntegral (fun v => (c.eta v:ℂ)) s rho gamma c.delta t := by
  rw [weightedReducedFormFactor_meanShape_integral s rho gamma hr1 hm c.chi c.eta
    c.chi_smooth c.eta_smooth (by linarith [c.H_pos,c.delta_pos]) c.small c.shape_support c.eta_support]
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  congr 1
  symm
  apply smoothMeanIntegral_eq_full _ _ _ _ _ _ c.delta_pos
  intro v hv
  have hz : c.eta v=0 := by
    by_contra hn
    linarith [c.eta_support v hn]
  simp only [hz,Complex.ofReal_zero]

theorem double_source_mean_integral (c : CompatibleYCutoffData n alpha beta U)
    (gamma : ℝ) (s : ℂ) (rho : ℝ) (hr1 : Real.exp rho < 1)
    (hm : (Real.exp rho)⁻¹-Real.exp rho < (sourceS s).im) :
    weightedDoubleFormFactor (n+1) (Real.exp rho) s (fixedYChartWeight gamma c.chi c.eta) =
      ((n+1).factorial:ℂ)⁻¹ * ∫ t : Fin n → ℝ, (c.chi t:ℂ)*
        smoothMeanIntegral (fun v => (c.eta v:ℂ)) s rho gamma c.delta t := by
  rw [weighted_residue_reduction (n+1) (Nat.succ_pos n) (Real.exp rho) s (globalRoot s)
    (fixedYChartWeight gamma c.chi c.eta)
    (fun theta => (globalRoot_admissible (Real.exp_pos rho) hr1 hm).toTuple (n+1) _
      (fun _ => anglePoint_norm (Real.exp_pos rho).le _))]
  exact c.source_mean_integral gamma s rho hr1 hm

/-- Exact all-order fixed-radius source derivative attachment. The shape
cutoff, mean cutoff, their support, and rho are held fixed throughout. -/
theorem source_mean_iteratedDeriv (c : CompatibleYCutoffData n alpha beta U)
    (gamma : ℝ) (s : ℂ) (rho : ℝ) (hr1 : Real.exp rho < 1)
    (hm : (Real.exp rho)⁻¹-Real.exp rho < (sourceS s).im) (j : ℕ) :
    iteratedDeriv j (fun z => weightedReducedFormFactor (n+1) (Real.exp rho) (globalRoot z)
      (fixedYChartWeight gamma c.chi c.eta)) s =
      ((n+1).factorial:ℂ)⁻¹ * iteratedDeriv j (fun z =>
        ∫ t : Fin n → ℝ, (c.chi t:ℂ)*smoothMeanIntegral
          (fun v => (c.eta v:ℂ)) z rho gamma c.delta t) s := by
  have he : (fun z => weightedReducedFormFactor (n+1) (Real.exp rho) (globalRoot z)
      (fixedYChartWeight gamma c.chi c.eta)) =ᶠ[𝓝 s]
      (fun z => ((n+1).factorial:ℂ)⁻¹ * ∫ t : Fin n → ℝ,
        (c.chi t:ℂ)*smoothMeanIntegral (fun v => (c.eta v:ℂ)) z rho gamma c.delta t) := by
    filter_upwards [dampingDomain_mem_nhds (dampingDomain_of_margin (Real.exp_pos rho) hr1 hm)] with z hz
    exact c.source_mean_integral gamma z rho hr1 hz.2
  rw [he.iteratedDeriv_eq j,iteratedDeriv_const_mul_field]

end CompatibleYCutoffData
end
end IsingBulk.First
