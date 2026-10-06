import IsingBulk.Tail.SelectedFSeriesBound
import IsingBulk.Tail.LargeCurrentSeries
import IsingBulk.Tail.OriginalKSSummability

/-! Actual summability needed by the all-order source comparison. The
bounds are derived internally and all three sequences use one selector. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch MeasureTheory
open scoped Topology

theorem common_source_summability (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ eta0 : ℝ, 0 < eta0 ∧ ∀ eta : ℝ, 0 < eta → eta < eta0 →
      ∃ alpha0 tau0 : ℝ, 0 < alpha0 ∧ 0 < tau0 ∧ ∀ alpha tau : ℝ,
        0 < alpha → alpha < alpha0 → 0 < tau → tau < tau0 →
        ∀ j : ℕ, ∃ e : ℝ, 0 < e ∧ ∀ eps cut : ℝ,
          0 < eps → eps < e → 0 < cut → cut ≤ 1 →
          Summable (fun n : ℕ => ‖iteratedDeriv j
            (selectedIntegral (2*(n+1)) (constructedSelector d.thetaB eta alpha)
              (Real.exp (-d.c₀*eps)) tau) (radialParameter d.theta eps)‖) ∧
          Summable (fun n : ℕ => ‖∫ lam in cut..1,
            differentiatedCurrentSlice (2*(n+1)) (constructedSelector d.thetaB eta alpha)
              (Real.exp (-d.c₀*eps)) tau lam j (radialParameter d.theta eps)‖) ∧
          Summable (fun N : ℕ => if 2≤N then
            originalKSNorm N (constructedSelector d.thetaB eta alpha) (Real.exp (-d.c₀*eps)) tau j
              (radialParameter d.theta eps) cut else 0) := by
  obtain ⟨etaF,tauF,heF,htF,hF⟩ := selected_actual_full_series_reqF d hcsmall
  obtain ⟨etaL,heL,hL⟩ := large_current_positive_even_series d hcsmall
  obtain ⟨etaK,heK,hK⟩ := actual_originalKS_summable d hcsmall
  have hb : 0 < Real.sin d.thetaB := Real.sin_pos_of_pos_of_lt_pi d.thetaB_pos d.thetaB_lt
  refine ⟨min etaF (min etaL etaK),lt_min heF (lt_min heL heK),?_⟩
  intro eta heta het
  obtain ⟨alphaL,tauL,haL,htL,hLL⟩ := hL eta heta (het.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨alphaK,tauK,haK,htK,hKK⟩ := hK eta heta (het.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨min alphaL (min alphaK (Real.sin d.thetaB/4)),min tauF (min tauL tauK),
    lt_min haL (lt_min haK (by positivity)),lt_min htF (lt_min htL htK),?_⟩
  intro alpha tau halpha halt htau htaut
  have haL' : alpha<alphaL := halt.trans_le (min_le_left _ _)
  have haK' : alpha<alphaK := halt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hab' : alpha<Real.sin d.thetaB/4 := halt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have htF' : tau<tauF := htaut.trans_le (min_le_left _ _)
  have htL' : tau<tauL := htaut.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have htK' : tau<tauK := htaut.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨eL,heL',hLs⟩ := hLL alpha tau halpha haL' htau htL'
  obtain ⟨eK,heK',hKs⟩ := hKK alpha tau halpha haK' htau htK'
  intro j
  obtain ⟨eF,CF,heF',_,hFs⟩ := hF eta alpha tau heta (het.trans_le (min_le_left _ _)) halpha hab' htau htF' j
  obtain ⟨CL,hCL,hLb⟩ := hLs j
  refine ⟨min eF (min eL eK),lt_min heF' (lt_min heL' heK'),?_⟩
  intro eps cut heps hepslt hcut hcut1
  exact ⟨(hFs eps heps (hepslt.trans_le (min_le_left _ _))).1,
    (hLb eps cut heps (hepslt.trans_le ((min_le_right _ _).trans (min_le_left _ _))) hcut hcut1).1,
    hKs j eps cut heps (hepslt.trans_le ((min_le_right _ _).trans (min_le_right _ _))) hcut.le hcut1⟩

end
end IsingBulk.Tail
