import IsingBulk.First.ActualLocalMeanAsymptotic
import IsingBulk.First.ActualLocalLowerBounds

/-! One common support for the actual leading asymptotic and all lower fixed
s-derivatives. The two source theorems are combined before selecting cutoffs. -/
namespace IsingBulk.First
noncomputable section
open Complex IsingBulk.Branch
open scoped Topology

theorem actual_local_full_profile {n : ℕ} (hn : 1 ≤ n) (a : OrderedChartData)
    (he : Even (n+1))
    (ha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I)=1)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I)=1) :
    let k := (n+1)^2/2-1
    localLeadingCoefficient a n k ≠ 0 ∧
    ∃ D : ℝ, 0 < D ∧ ∀ delta : ℝ, 0 < delta → delta ≤ D →
      ∃ R e : ℝ, 0 < R ∧ 0 < e ∧
        ∀ eta : ℝ → ℂ, Continuous eta → (∀ v : ℝ, |v| ≤ delta → eta v=1) →
        ∀ chi : ShapeSpace n → ℂ, Continuous chi → chi 0=1 → (∀ x, ‖chi x‖ ≤ 1) →
          (∀ x, chi x ≠ 0 → ‖x‖ < R) →
          Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
            (fun epsilon => (deriv^[k] (localizedSmoothMeanIntegral a chi eta
              (-(Real.sin a.theta/4)*epsilon) delta)) (radialParameter a.theta epsilon)-
              (Real.sqrt epsilon:ℂ)⁻¹*localLeadingCoefficient a n k)
            (fun epsilon => (Real.sqrt epsilon:ℂ)⁻¹) ∧
          (∀ j : ℕ, j < k → ∃ C : ℝ, 0 < C ∧ ∀ epsilon : ℝ,
            0 < epsilon → epsilon < e →
            ‖(deriv^[j] (localizedSmoothMeanIntegral a chi eta
              (-(Real.sin a.theta/4)*epsilon) delta)) (radialParameter a.theta epsilon)‖ ≤ C) := by
  dsimp only
  obtain ⟨hL,Dt,hDt,hTop⟩ := actual_local_mean_source_asymptotic hn a he ha hb
  obtain ⟨Dl,hDl,hLow⟩ := actual_smooth_local_lower_bounds hn a he ha hb
  refine ⟨hL,min Dt Dl,lt_min hDt hDl,?_⟩
  intro delta hd hdD
  obtain ⟨Rt,hRt,hT⟩ := hTop delta hd (hdD.trans (min_le_left _ _))
  obtain ⟨Rl,e,hRl,heps,hB⟩ := hLow delta hd (hdD.trans (min_le_right _ _))
  refine ⟨min Rt Rl,e,lt_min hRt hRl,heps,?_⟩
  intro eta heta heta1 chi hchi hchi0 hchib hchis
  exact ⟨hT eta heta heta1 chi hchi hchi0 hchib
      (fun x hx => (hchis x hx).trans_le (min_le_left _ _)),
    hB eta heta heta1 chi hchi hchib (fun x hx => (hchis x hx).trans_le (min_le_right _ _))⟩

end
end IsingBulk.First
