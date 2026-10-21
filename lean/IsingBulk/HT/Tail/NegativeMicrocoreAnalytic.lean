import IsingBulk.HT.Tail.NegativeMicrocoreVariableAnalytic
import IsingBulk.Tail.MicrocoreComplexChart
namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.Tail IsingBulk.Jets IsingBulk.Lie
open scoped BigOperators
theorem negativeMicrocorePhaseFactor_analytic {N : ℕ} (φ : Fin N → ℂ)
    (hZ : 1+Complex.exp (-Complex.I*∑ i, φ i) ≠ 0) :
    AnalyticAt ℂ negativeMicrocorePhaseFactor φ := by
  have hp : AnalyticAt ℂ (@microcoreVandermondeSquared N) φ := by
    unfold microcoreVandermondeSquared
    apply Finset.analyticAt_fun_prod
    intro i _
    apply Finset.analyticAt_fun_prod
    intro j _
    exact (((ContinuousLinearMap.proj (R := ℂ) i).analyticAt φ).sub
      ((ContinuousLinearMap.proj (R := ℂ) j).analyticAt φ)).pow 2
  have hd : AnalyticAt ℂ (fun ψ : Fin N → ℂ => 1+Complex.exp (-Complex.I*∑ i, ψ i)) φ := by
    exact analyticAt_const.add ((analyticAt_const.mul (Finset.analyticAt_fun_sum _
      (fun i _ => (ContinuousLinearMap.proj (R := ℂ) i).analyticAt φ))).cexp)
  exact hp.div hd hZ

theorem negativeMicroRegularDensity_analytic {N : ℕ} (z : ℂ × (Fin N → ℂ))
    (hF : AnalyticAt ℂ negativeMicrocoreVariableFactor z) (hZ : 1+regularZProduct z.1 z.2 ≠ 0) :
    AnalyticAt ℂ (fun t : ℂ × (Fin N → ℂ) => negativeMicroRegularDensity t.1 t.2) z := by
  have hp := (negativeMicrocorePhaseFactor_analytic z.2 hZ).comp (f := fun t : ℂ × (Fin N → ℂ) => t.2) analyticAt_snd
  have he : (fun t : ℂ × (Fin N → ℂ) => negativeMicroRegularDensity t.1 t.2)=
      (fun t => negativeMicrocorePhaseFactor t.2*negativeMicrocoreVariableFactor t) := by
    funext t
    exact negativeMicroRegularDensity_phase_factor t.1 t.2
  rw [he]
  exact hp.mul hF


end
end IsingBulk.HT.Tail
