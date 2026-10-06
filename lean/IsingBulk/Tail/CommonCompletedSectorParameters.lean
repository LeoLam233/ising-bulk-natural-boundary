import IsingBulk.Tail.SelectedFAsymptotic
import IsingBulk.Tail.LargeCurrentAsymptotic
import IsingBulk.Tail.HighKSTail

/-! One acyclic selector choice for the completed quantitative sectors.
This theorem proves its conclusions from the actual source endpoints; it
introduces no hypothesis carrying any missing intermediate-sector estimate. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Filter Asymptotics MeasureTheory
open scoped Topology

theorem common_completed_sector_parameters (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ eta0 : ℝ, 0 < eta0 ∧ ∀ eta : ℝ, 0 < eta → eta < eta0 →
      ∃ alpha0 tau0 : ℝ, 0 < alpha0 ∧ 0 < tau0 ∧ ∀ alpha tau : ℝ,
        0 < alpha → alpha < alpha0 → 0 < tau → tau < tau0 →
        RegularSelector (constructedSelector d.thetaB eta alpha) ∧
        (∀ j : ℕ, (fun eps : ℝ => ∑' n : ℕ, ‖iteratedDeriv j
          (selectedIntegral (2*(n+1)) (constructedSelector d.thetaB eta alpha)
            (Real.exp (-d.c₀*eps)) tau) (radialParameter d.theta eps)‖)
          =o[𝓝[>] 0] (fun eps : ℝ => (Real.sqrt eps)⁻¹)) ∧
        (∀ (j : ℕ) (beta : ℝ), 0 < beta → beta*((j:ℝ)+1)<1/2 →
          (fun eps : ℝ => ∑' n : ℕ, ‖∫ lam in (eps^beta)..1,
            differentiatedCurrentSlice (2*(n+1)) (constructedSelector d.thetaB eta alpha)
              (Real.exp (-d.c₀*eps)) tau lam j (radialParameter d.theta eps)‖)
            =o[𝓝[>] 0] (fun eps : ℝ => (Real.sqrt eps)⁻¹)) ∧
        (∀ (k : ℕ) (Q : ℝ), 0 ≤ Q → ∃ D : ℝ, 0 < D ∧ ∀ j : ℕ, j ≤ k →
          ∀ beta : ℝ, 0 ≤ beta → Tendsto
            (fun eps : ℝ => highKSNormTail d eta alpha tau j D eps (eps^beta)/eps^Q)
            (𝓝[>] 0) (𝓝 0)) := by
  obtain ⟨etaF,tauF,heF,htF,hF⟩ := selected_actual_full_series_littleO d hcsmall
  obtain ⟨etaL,heL,hL⟩ := large_current_positive_even_littleo d hcsmall
  obtain ⟨etaK,heK,hK⟩ := actual_highKS_epsilon_tail_finite_j d hcsmall
  have hb : 0 < Real.sin d.thetaB := Real.sin_pos_of_pos_of_lt_pi d.thetaB_pos d.thetaB_lt
  let eta0 := min etaF (min etaL (min etaK (Real.sin d.thetaB/4)))
  have he0 : 0 < eta0 := lt_min heF (lt_min heL (lt_min heK (by positivity)))
  refine ⟨eta0,he0,?_⟩
  intro eta heta het
  have hetF : eta<etaF := het.trans_le (min_le_left _ _)
  have hetL : eta<etaL := het.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hetK : eta<etaK := het.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hetb : eta≤Real.sin d.thetaB/4 := het.le.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨alphaL,tauL,haL,htL,hLL⟩ := hL eta heta hetL
  obtain ⟨alphaK,tauK,haK,htK,hKK⟩ := hK eta heta hetK
  let alpha0 := min alphaL (min alphaK (Real.sin d.thetaB/4))
  let tau0 := min tauF (min tauL tauK)
  refine ⟨alpha0,tau0,lt_min haL (lt_min haK (by positivity)),lt_min htF (lt_min htL htK),?_⟩
  intro alpha tau halpha halt htau htaut
  have haL' : alpha<alphaL := halt.trans_le (min_le_left _ _)
  have haK' : alpha<alphaK := halt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hab' : alpha<Real.sin d.thetaB/4 := halt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have htF' : tau<tauF := htaut.trans_le (min_le_left _ _)
  have htL' : tau<tauL := htaut.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have htK' : tau<tauK := htaut.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  exact ⟨constructedSelector_regular d.thetaB eta alpha hb heta hetb halpha,
    hF eta alpha tau heta hetF halpha hab' htau htF',
    hLL alpha tau halpha haL' htau htL',hKK alpha tau halpha haK' htau htK'⟩

end
end IsingBulk.Tail
