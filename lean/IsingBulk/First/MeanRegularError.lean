import IsingBulk.First.MeanEdgeBounds

/-! The literal mean error is the sum of displaced contour sides and fixed
real cutoff edges. No Taylor model replaces either contribution. -/
namespace IsingBulk.First
noncomputable section
open Complex
open scoped Topology

def meanRegularError {n : ℕ} (eta : ℝ → ℂ) (s : ℂ) (rho alpha delta : ℝ) (t : Fin n → ℝ) : ℂ :=
  displacedMeanSides s rho alpha delta delta t + meanCutoffEdges eta s rho alpha delta t

theorem actual_mean_regular_error_bounds (a : OrderedChartData) (n : ℕ)
    (halpha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I)=1)
    (hbeta : exp (-(n+1:ℂ)*(a.beta:ℂ)*I)=1) :
    ∃ D : ℝ, 0 < D ∧ ∀ delta : ℝ, 0 < delta → delta ≤ D →
      ∃ r : ℝ, 0 < r ∧ ∀ eta : ℝ → ℂ, Continuous eta →
      (∀ (rho : ℝ) (t : Fin n → ℝ), ‖(rho,t)‖ ≤ r → ∀ s : ℂ,
        ‖s-exp ((a.theta:ℂ)*I)‖ < r →
        AnalyticAt ℂ (fun z => meanRegularError eta z rho a.alpha delta t) s) ∧
      (∀ j : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (rho : ℝ) (t : Fin n → ℝ), ‖(rho,t)‖ ≤ r →
        ∀ s : ℂ, ‖s-exp ((a.theta:ℂ)*I)‖ < r →
        ‖(deriv^[j] (fun z => meanRegularError eta z rho a.alpha delta t)) s‖ ≤ C) := by
  obtain ⟨Ds,hDs,hS⟩ := actual_displaced_mean_sides_bounds a n halpha hbeta
  obtain ⟨De,hDe,hE⟩ := actual_mean_cutoff_edges_bounds a n halpha hbeta
  refine ⟨min Ds De,lt_min hDs hDe,?_⟩
  intro delta hd hdD
  obtain ⟨rs,hrs,haS,hbS⟩ := hS delta hd (hdD.trans (min_le_left _ _))
  obtain ⟨re,hre,hE'⟩ := hE delta hd (hdD.trans (min_le_right _ _))
  refine ⟨min rs re,lt_min hrs hre,?_⟩
  intro eta heta
  obtain ⟨haE,hbE⟩ := hE' eta heta
  have hAnalytic (rho : ℝ) (t : Fin n → ℝ) (ht : ‖(rho,t)‖ ≤ min rs re) (s : ℂ)
      (hs : ‖s-exp ((a.theta:ℂ)*I)‖ < min rs re) :
      AnalyticAt ℂ (fun z => displacedMeanSides z rho a.alpha delta delta t) s ∧
      AnalyticAt ℂ (fun z => meanCutoffEdges eta z rho a.alpha delta t) s :=
    ⟨haS rho t (ht.trans (min_le_left _ _)) s (hs.trans_le (min_le_left _ _)),
      haE rho t (ht.trans (min_le_right _ _)) s (hs.trans_le (min_le_right _ _))⟩
  constructor
  · intro rho t ht s hs
    exact (hAnalytic rho t ht s hs).1.add (hAnalytic rho t ht s hs).2
  · intro j
    obtain ⟨Cs,hCs,hbs⟩ := hbS j
    obtain ⟨Ce,hCe,hbe⟩ := hbE j
    refine ⟨Cs+Ce,by positivity,?_⟩
    intro rho t ht s hs
    obtain ⟨haS',haE'⟩ := hAnalytic rho t ht s hs
    simp only [← iteratedDeriv_eq_iterate] at *
    unfold meanRegularError
    rw [iteratedDeriv_fun_add haS'.contDiffAt haE'.contDiffAt]
    exact (norm_add_le _ _).trans (add_le_add
      (hbs rho t (ht.trans (min_le_left _ _)) s (hs.trans_le (min_le_left _ _)))
      (hbe rho t (ht.trans (min_le_right _ _)) s (hs.trans_le (min_le_right _ _))))

end
end IsingBulk.First
