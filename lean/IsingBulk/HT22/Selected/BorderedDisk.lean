import IsingBulk.HT22.Selected.AllOrderRows
import IsingBulk.HT22.Selected.BorderRowBounds
import IsingBulk.HT22.Selected.RootBounds

/-! Actual selected-disk odd-border control. The particle count is arbitrary
positive N; no even-N endpoint is used. -/
namespace IsingBulk.HT22.Selected
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Algebra
open scoped BigOperators

 theorem selected_bordered_kernel_disk (d : PreferredBranchData) {cap : ℝ} (hcap : 0<cap) :
    ∃ c ρ : ℝ, 0<c ∧ 0<ρ ∧ ρ≤1 ∧ ∀ τ : ℝ, 0<τ → τ<ρ →
      ∃ K : ℝ, 0<K ∧ ∀ N : ℕ, 0<N → ∀ ε : ℝ, 0<ε → ε<ρ →
      ∀ θ : Fin N → ℝ,
      preferredFullPopulationWeight preferredPopulationCutoff
        (cappedCanonicalPreferredBump d cap hcap).p
        (cappedCanonicalPreferredBump d cap hcap).m θ≠0 →
      ∀ t : ℂ, ‖t-IsingBulk.Branch.radialParameter d.alpha ε‖≤c*τ^2/(N:ℝ)^3 →
      (∀ i, AnalyticAt ℂ (preferredSelectedContinuedRoot d
        (cappedCanonicalPreferredBump d cap hcap) ε τ θ i) t) ∧
      (∀ i j, 1-preferredSelectedContinuedRoot d
        (cappedCanonicalPreferredBump d cap hcap) ε τ θ i t*
        preferredSelectedContinuedRoot d (cappedCanonicalPreferredBump d cap hcap) ε τ θ j t≠0) ∧
      ‖(constantBorderFirst
        (preferredSelectedAngularRoot d (cappedCanonicalPreferredBump d cap hcap) τ θ)
        (fun i => preferredSelectedContinuedRoot d
          (cappedCanonicalPreferredBump d cap hcap) ε τ θ i t)).det‖≤
        (K*Real.sqrt (N+1))^(N+1) := by
  obtain ⟨c₁,ρ₁,hc₁,hρ₁,hρ₁1,hrows⟩ := selected_gauge_rows_all_orders d hcap
  obtain ⟨c₂,J,ρ₂,hc₂,hJ,hρ₂,_hρ₂1,hinv⟩ := selected_inverse_root_disk d hcap
  let c := min c₁ c₂
  let ρ := min ρ₁ ρ₂
  have hc : 0<c := lt_min hc₁ hc₂
  have hρ : 0<ρ := lt_min hρ₁ hρ₂
  have hρ1 : ρ≤1 := (min_le_left _ _).trans hρ₁1
  refine ⟨c,ρ,hc,hρ,hρ1,?_⟩
  intro τ hτ hτρ
  obtain ⟨K,hK,hrow⟩ := hrows τ hτ (hτρ.trans_le (min_le_left _ _))
  let E := Real.exp 1
  let A := E*J*K
  have hA : 0<A := by dsimp [A,E]; positivity
  refine ⟨A+1,by positivity,?_⟩
  intro N hN ε hε hερ θ hw t ht
  let B := cappedCanonicalPreferredBump d cap hcap
  let y := preferredSelectedAngularRoot d B τ θ
  let z := fun i => preferredSelectedContinuedRoot d B ε τ θ i t
  have hrad (c' : ℝ) (hcc : c≤c') :
      ‖t-IsingBulk.Branch.radialParameter d.alpha ε‖≤c'*τ^2/(N:ℝ)^3 :=
    ht.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcc (sq_nonneg _)) (by positivity))
  obtain ⟨ha,hgap,hr⟩ := hrow N hN ε hε (hερ.trans_le (min_le_left _ _)) θ hw t
    (hrad c₁ (min_le_left _ _))
  have hz := hinv N hN ε τ hε (hερ.trans_le (min_le_right _ _)) hτ
    (hτρ.trans_le (min_le_right _ _)) θ hw t (hrad c₂ (min_le_right _ _))
  have hordinary := ordinary_rows_of_gauge y z (Real.exp_pos 1).le hJ.le
    (fun i => Complex.exp_ne_zero _) (fun i => (hz i).1)
    (fun i => selected_angular_root_bound hN d B hτ.le (hτρ.le.trans hρ1) θ i)
    (fun i => (hz i).2) hr
  have hb : ∀ i, (∑ j, ‖ordinaryEntry (y i) (y j) (z i) (z j)‖^2)≤A^2*N := by
    intro i
    exact (hordinary i).trans_eq (by dsimp [A,E]; ring)
  exact ⟨ha,hgap,ghostBorder_det_bound _ hA.le hb⟩

end
end IsingBulk.HT22.Selected
