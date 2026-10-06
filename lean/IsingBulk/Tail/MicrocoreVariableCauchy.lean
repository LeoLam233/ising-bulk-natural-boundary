import IsingBulk.Tail.MicrocoreYMotion
import IsingBulk.Tail.MicrocoreAmplitudeAnalytic
import IsingBulk.Tail.MicrocoreDensityAllOrder
import IsingBulk.First.DominatedAnalyticIntegral

/-! Fixed-phase Cauchy bounds for the actual variable microcore factor.
The disk is protected by the actual Y gap and the proved product motion. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets IsingBulk.Branch Metric
open scoped BigOperators

def microcoreVariableRadius (r g C : ℝ) (N : ℕ) : ℝ := min (r/2) (g/(2*(N:ℝ)*C^N))

theorem microcore_variable_cauchy_uniform (s₀ : ℂ) (c : ℝ) (hs₀ : s₀ ≠ 0)
    (hS : s₀+s₀⁻¹=(1+c:ℂ)) (hc : |c|<1) :
    ∃ A C r : ℝ, 0 < A ∧ 1 ≤ C ∧ 0 < r ∧ ∀ N : ℕ, 1 ≤ N →
      ∀ φ : Fin N → ℂ, (∀ i, ‖φ i‖ < r) → ∀ s : ℂ, ‖s-s₀‖ < r/2 →
      ∀ g : ℝ, 0 < g → g ≤ ‖1-regularYProduct s φ‖ → ∀ j : ℕ,
      ‖iteratedDeriv j (fun t => microcoreVariableFactor (t,φ)) s‖ ≤
        j.factorial*(2*Real.exp (A*(N:ℝ)^2)/g)/(microcoreVariableRadius r g C N)^j := by
  obtain ⟨C,rY,hC,hrY,hY⟩ := regularY_product_motion_uniform s₀ c hs₀ hS hc
  obtain ⟨A,rA,hA,hrA,hAmp⟩ := micro_amplitude_uniform_analytic_bound s₀ c hs₀ hS hc
  obtain ⟨Cy,ry,_,hry,hy⟩ := regularY_parameter_uniform s₀ c hs₀ hS hc
  let r := min rY (min rA ry)
  have hr : 0 < r := lt_min hrY (lt_min hrA hry)
  have hrY' : r ≤ rY := min_le_left _ _
  have hrA' : r ≤ rA := (min_le_right _ _).trans (min_le_left _ _)
  have hry' : r ≤ ry := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨A,C,r,hA,hC,hr,?_⟩
  intro N hN φ hφ s hs g hg hgap j
  have hNr : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hCp : 0 < C := by linarith
  let δ := microcoreVariableRadius r g C N
  have hδ : 0 < δ := by unfold δ microcoreVariableRadius; positivity
  have hδr : δ ≤ r/2 := min_le_left _ _
  have hδg : δ ≤ g/(2*(N:ℝ)*C^N) := min_le_right _ _
  have hcenter : ‖s-s₀‖ < r := hs.trans (half_lt_self hr)
  have hmem : ∀ t ∈ closedBall s δ, ‖t-s₀‖ < r := by
    intro t ht
    have ht' : ‖t-s‖ ≤ δ := by simpa [mem_closedBall,dist_eq_norm] using ht
    calc
      _ ≤ ‖t-s‖+‖s-s₀‖ := norm_sub_le_norm_sub_add_norm_sub t s s₀
      _ < r := by linarith
  have hgap' : ∀ t ∈ closedBall s δ, g/2 ≤ ‖1-regularYProduct t φ‖ := by
    intro t ht
    have ht' : ‖t-s‖ ≤ δ := by simpa [mem_closedBall,dist_eq_norm] using ht
    have hm := hY N φ (fun i => (hφ i).trans_le hrY') s t
      (hcenter.trans_le hrY') ((hmem t ht).trans_le hrY')
    have hbudget := (le_div_iff₀ (show 0 < 2*(N:ℝ)*C^N by positivity)).mp hδg
    have hnorm := norm_sub_norm_le (1-regularYProduct s φ) (1-regularYProduct t φ)
    have he : (1-regularYProduct s φ)-(1-regularYProduct t φ)=regularYProduct t φ-regularYProduct s φ := by ring
    rw [he] at hnorm
    have hh := mul_le_mul_of_nonneg_left ht' (show 0 ≤ (N:ℝ)*C^N by positivity)
    nlinarith
  have han : ∀ t ∈ closedBall s δ,
      AnalyticAt ℂ (fun z => microcoreVariableFactor (z,φ)) t := by
    intro t ht
    have ha := (hAmp N hN t φ ((hmem t ht).trans_le hrA')
      (fun i => (hφ i).trans_le hrA')).1
    have hay : AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => regularYProduct z.1 z.2) (t,φ) := by
      apply Finset.analyticAt_fun_prod
      intro i _
      exact AnalyticAt.comp (g := fun z : ℂ × ℂ => regularY z.1 z.2)
        (f := fun z : ℂ × (Fin N → ℂ) => (z.1,z.2 i))
        (hy t (φ i) ((hmem t ht).trans_le hry') ((hφ i).trans_le hry')).1
        (analyticAt_fst.prod (analytic_coordinate i _))
    have hne : 1-regularYProduct t φ ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) (hgap' t ht))
    have hh := ha.div (analyticAt_const.sub hay) hne
    have hc' := AnalyticAt.comp
      (g := fun z : ℂ × (Fin N → ℂ) => microRegularAmplitude z.1 z.2/(1-regularYProduct z.1 z.2))
      (f := fun z : ℂ => (z,φ)) hh (analyticAt_id.prod analyticAt_const)
    convert! hc' using 1
  have hb : ∀ t ∈ closedBall s δ,
      ‖microcoreVariableFactor (t,φ)‖ ≤ 2*Real.exp (A*(N:ℝ)^2)/g := by
    intro t ht
    have ha := (hAmp N hN t φ ((hmem t ht).trans_le hrA')
      (fun i => (hφ i).trans_le hrA')).2
    unfold microcoreVariableFactor
    rw [norm_div]
    calc
      _ ≤ Real.exp (A*(N:ℝ)^2)/(g/2) := div_le_div₀ (by positivity) ha (by positivity) (hgap' t ht)
      _ = _ := by ring
  exact IsingBulk.First.cauchy_bound_on_subdisk han hb hδ (fun _ ht => ht) j

end
end IsingBulk.Tail
