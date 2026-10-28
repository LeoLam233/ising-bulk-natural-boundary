import IsingBulk.Preferred22.SelectedProductDisk

/-! F001 signed product continuation uses the same proven full product
attenuation, not positivity of a complex product or a reset square root. -/
namespace IsingBulk.HT22.Selected
noncomputable section
open IsingBulk.Preferred22

theorem signed_resolvent_attenuation (σ z : ℂ) (hσ : ‖σ‖=1)
    {x : ℝ} (hx : 0<x) (hx1 : x≤1) (hz : ‖z‖≤Real.exp (-x)) :
    ‖(1+σ*z)/(1-σ*z)‖≤2*Real.exp 1/x := by
  exact preferred_resolvent_of_attenuation hx hx1 (by simpa only [norm_mul,hσ,one_mul] using hz)

theorem selected_signed_product_disk (d : PreferredBranchData) {cap : ℝ} (hcap : 0<cap) :
    ∃ c C ρ : ℝ, 0<c ∧ 0<C ∧ 0<ρ ∧ ρ≤1 ∧
      ∀ N : ℕ, 0<N → ∀ ε τ : ℝ, 0<ε → ε<ρ → 0<τ → τ<ρ →
      ∀ θ : Fin N → ℝ,
      preferredFullPopulationWeight preferredPopulationCutoff
        (cappedCanonicalPreferredBump d cap hcap).p
        (cappedCanonicalPreferredBump d cap hcap).m θ≠0 →
      ∀ t : ℂ, ‖t-IsingBulk.Branch.radialParameter d.alpha ε‖≤c*τ^2/(N:ℝ)^3 →
      ∀ σ : ℂ, ‖σ‖=1 →
      AnalyticAt ℂ (preferredSelectedContinuedProduct d
        (cappedCanonicalPreferredBump d cap hcap) ε τ θ) t ∧
      1-σ*preferredSelectedContinuedProduct d
        (cappedCanonicalPreferredBump d cap hcap) ε τ θ t≠0 ∧
      ‖(1+σ*preferredSelectedContinuedProduct d
        (cappedCanonicalPreferredBump d cap hcap) ε τ θ t)/
        (1-σ*preferredSelectedContinuedProduct d
        (cappedCanonicalPreferredBump d cap hcap) ε τ θ t)‖≤C*(N:ℝ)/τ := by
  obtain ⟨c,C₀,ρ,hc,_hC₀,hρ,hρ1,hraw⟩ := preferred_selected_continued_product_disk d hcap
  let c' := min c 1
  have hc' : 0<c' := lt_min hc zero_lt_one
  refine ⟨c',2*Real.exp 1/c',ρ,hc',by positivity,hρ,hρ1,?_⟩
  intro N hN ε τ hε hερ hτ hτρ θ hw t ht σ hσ
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hn1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hτ1 : τ≤1 := hτρ.le.trans hρ1
  have hcc : c'≤c := min_le_left _ _
  have hc1 : c'≤1 := min_le_right _ _
  have hrad : ‖t-IsingBulk.Branch.radialParameter d.alpha ε‖≤c*τ^2/(N:ℝ)^3 :=
    ht.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcc (sq_nonneg _)) (by positivity))
  obtain ⟨ha,hZ,_hres⟩ := hraw N hN ε τ hε hερ hτ hτρ θ hw t hrad
  let Z := preferredSelectedContinuedProduct d (cappedCanonicalPreferredBump d cap hcap) ε τ θ t
  let x := c'*τ/(N:ℝ)
  have hx : 0<x := by dsimp [x]; positivity
  have hx1 : x≤1 := by
    apply (div_le_one₀ hn).mpr
    nlinarith [mul_le_mul hc1 hτ1 hτ.le (by norm_num : (0:ℝ)≤1)]
  have hz : ‖Z‖≤Real.exp (-x) := hZ.trans (Real.exp_le_exp.mpr (by
    dsimp [x]
    exact neg_le_neg (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcc hτ.le) hn.le)))
  have hinside : ‖σ*Z‖<1 := by
    rw [norm_mul,hσ,one_mul]
    exact hz.trans_lt (Real.exp_lt_one_iff.mpr (by linarith))
  have hgap : 1-σ*Z≠0 := by
    intro he
    rw [←sub_eq_zero.mp he,norm_one] at hinside
    exact lt_irrefl _ hinside
  refine ⟨ha,hgap,?_⟩
  have hh := signed_resolvent_attenuation σ Z hσ hx hx1 hz
  have he : 2*Real.exp 1/x=(2*Real.exp 1/c')*(N:ℝ)/τ := by
    dsimp [x]
    field_simp
  exact hh.trans_eq he

end
end IsingBulk.HT22.Selected
