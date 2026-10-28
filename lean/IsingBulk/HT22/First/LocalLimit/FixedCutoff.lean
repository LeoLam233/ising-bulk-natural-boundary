import IsingBulk.HT22.First.LocalLimit.TwoCharts
import IsingBulk.First.SmoothCutoffConstruction

namespace IsingBulk.HT22.LocalLimit
noncomputable section
open Complex Set Filter Metric IsingBulk.First IsingBulk.HT.First IsingBulk.Branch
open scoped Topology ContDiff

/-- A genuine fixed real-smooth cutoff is constructed, so the local theorem
is not vacuous in its test-function hypotheses. -/
theorem exists_equalAngle_two_chart_asymptotic {n : ℕ} (hn : 1≤n) (ho : Odd (n+1))
    (α : ℝ) (hα : 0<α) (hαπ : α<Real.pi) (hc : Real.cos α≠0)
    (ha : exp (-(n+1:ℂ)*(α:ℂ)*I)=1) :
    ∃ χ : ShapeSpace n → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ x,0≤χ x ∧ χ x≤1) ∧ χ =ᶠ[𝓝 0] (fun _ => 1) ∧
      Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
        (fun ε => (deriv^[derivativeOrder (n+1)]
          (angularTwoChartIntegral α (fun x => (χ x:ℂ)))) (radialParameter α ε)-
          (ε:ℂ)⁻¹*equalAngleLeadingCoefficient (n+1) α)
        (fun ε => (ε:ℂ)⁻¹) := by
  obtain ⟨R,hR,h⟩ := equalAngle_two_chart_asymptotic hn ho α hα hαπ hc ha
  obtain ⟨χ,hcχ,hcomp,hbounds,hone,hsupp⟩ := exists_fixed_smooth_cutoff
    (0:ShapeSpace n) (ball_mem_nhds (0:ShapeSpace n) hR)
  refine ⟨χ,hcχ,hcomp,hbounds,hone,h _ ?_ ?_ ?_ ?_⟩
  · exact continuous_ofReal.comp hcχ.continuous
  · exact_mod_cast hone.eq_of_nhds
  · intro x
    rw [norm_real,Real.norm_eq_abs,abs_of_nonneg (hbounds x).1]
    exact (hbounds x).2
  · intro x hx
    apply mem_ball_zero_iff.mp (hsupp _)
    apply subset_tsupport χ
    simpa only [Function.mem_support,ofReal_ne_zero] using hx

end
end IsingBulk.HT22.LocalLimit
