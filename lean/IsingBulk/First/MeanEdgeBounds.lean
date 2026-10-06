import IsingBulk.First.MeanSideBounds

/-! The smooth-to-hard mean cutoff edges are genuine regular compact source
integrals. The fixed cutoff is evaluated only at real mean variables. -/
namespace IsingBulk.First
noncomputable section
open Set Complex MeasureTheory
open scoped Topology

def meanCutoffEdges {n : ℕ} (eta : ℝ → ℂ) (s : ℂ) (rho alpha delta : ℝ) (t : Fin n → ℝ) : ℂ :=
  (∫ x in Icc (-2*delta) (-delta), eta x * meanLocalDensity s rho alpha t (x:ℂ)) +
    ∫ x in Icc delta (2*delta), eta x * meanLocalDensity s rho alpha t (x:ℂ)

theorem meanLeftEdge_annulus {delta : ℝ} (hd : 0 < delta) :
    MapsTo (fun x : ℝ => (x:ℂ)) (Icc (-2*delta) (-delta)) (meanSeparatedAnnulus delta) := by
  intro x hx
  change delta/2 ≤ ‖(x:ℂ)‖ ∧ ‖(x:ℂ)‖ ≤ 2*delta
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_neg (by linarith [hx.2])]
  constructor <;> linarith [hx.1,hx.2]

theorem meanRightEdge_annulus {delta : ℝ} (hd : 0 < delta) :
    MapsTo (fun x : ℝ => (x:ℂ)) (Icc delta (2*delta)) (meanSeparatedAnnulus delta) := by
  intro x hx
  change delta/2 ≤ ‖(x:ℂ)‖ ∧ ‖(x:ℂ)‖ ≤ 2*delta
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith [hx.1])]
  constructor <;> linarith [hx.1,hx.2]

theorem actual_mean_cutoff_edges_bounds (a : OrderedChartData) (n : ℕ)
    (halpha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I)=1)
    (hbeta : exp (-(n+1:ℂ)*(a.beta:ℂ)*I)=1) :
    ∃ D : ℝ, 0 < D ∧ ∀ delta : ℝ, 0 < delta → delta ≤ D →
      ∃ r : ℝ, 0 < r ∧ ∀ eta : ℝ → ℂ, Continuous eta →
      (∀ (rho : ℝ) (t : Fin n → ℝ), ‖(rho,t)‖ ≤ r → ∀ s : ℂ,
        ‖s-exp ((a.theta:ℂ)*I)‖ < r →
        AnalyticAt ℂ (fun z => meanCutoffEdges eta z rho a.alpha delta t) s) ∧
      (∀ j : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (rho : ℝ) (t : Fin n → ℝ), ‖(rho,t)‖ ≤ r →
        ∀ s : ℂ, ‖s-exp ((a.theta:ℂ)*I)‖ < r →
        ‖(deriv^[j] (fun z => meanCutoffEdges eta z rho a.alpha delta t)) s‖ ≤ C) := by
  obtain ⟨D,hD,hTube⟩ := actual_mean_separated_integrals a n halpha hbeta
  refine ⟨D,hD,?_⟩
  intro delta hd hdD
  obtain ⟨r,hr,hInt⟩ := hTube delta hd hdD
  refine ⟨r,hr,?_⟩
  intro eta heta
  have hL := hInt (Icc (-2*delta) (-delta)) isCompact_Icc (fun x : ℝ => (x:ℂ))
    Complex.continuous_ofReal (meanLeftEdge_annulus hd) eta heta.continuousOn
  have hR := hInt (Icc delta (2*delta)) isCompact_Icc (fun x : ℝ => (x:ℂ))
    Complex.continuous_ofReal (meanRightEdge_annulus hd) eta heta.continuousOn
  constructor
  · intro rho t ht s hs
    exact (hL.1 rho t ht s hs).add (hR.1 rho t ht s hs)
  · intro j
    obtain ⟨CL,hCL,hl⟩ := hL.2.2 j
    obtain ⟨CR,hCR,hr'⟩ := hR.2.2 j
    refine ⟨CL+CR,by positivity,?_⟩
    intro rho t ht s hs
    have haL := hL.1 rho t ht s hs
    have haR := hR.1 rho t ht s hs
    simp only [← iteratedDeriv_eq_iterate] at *
    unfold meanCutoffEdges
    rw [iteratedDeriv_fun_add haL.contDiffAt haR.contDiffAt]
    exact (norm_add_le _ _).trans (add_le_add (hl rho t ht s hs) (hr' rho t ht s hs))

end
end IsingBulk.First
