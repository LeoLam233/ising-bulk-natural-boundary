import IsingBulk.HT22.Selected.ContinuedDensity
import IsingBulk.Preferred22.ZerothSourceBound

/-! Actual odd-bordered density bounds on one common disk, uniform in N
and angular configuration. The N+1 border is retained literally. -/
namespace IsingBulk.HT22.Selected
noncomputable section
open IsingBulk.Preferred22 Set
open scoped BigOperators

theorem selected_density_disk (d : PreferredBranchData) {cap : ℝ} (hcap : 0<cap) :
    ∃ c H A J ρ : ℝ, 0<c ∧ 0<H ∧ 0<A ∧ 0<J ∧ 0<ρ ∧ ρ≤1 ∧
      ∀ τ : ℝ, 0<τ → τ<ρ → ∃ K : ℝ, 0<K ∧
      ∀ N : ℕ, 0<N → ∀ ε : ℝ, 0<ε → ε<ρ → ∀ θ : Fin N → ℝ,
      preferredFullPopulationWeight preferredPopulationCutoff
        (cappedCanonicalPreferredBump d cap hcap).p
        (cappedCanonicalPreferredBump d cap hcap).m θ≠0 →
      ∀ t : ℂ, ‖t-IsingBulk.Branch.radialParameter d.alpha ε‖≤c*τ^2/(N:ℝ)^3 →
      ∀ σ : ℂ, ‖σ‖=1 →
      AnalyticAt ℂ (selectedContinuedDensity σ d
        (cappedCanonicalPreferredBump d cap hcap) ε τ θ) t ∧
      ‖selectedContinuedDensity σ d (cappedCanonicalPreferredBump d cap hcap) ε τ θ t‖≤
        (J^N*(H*(N:ℝ)/τ)*(K*Real.sqrt (N+1))^(N+1)*A^N /
          ((N.factorial:ℝ)*(2*Real.pi)^(N-1))) *
          (∏ i,preferredSelectedOneBodyProfile d ε (θ i)) := by
  obtain ⟨ck,ρk,hck,hρk,_hρk1,hkb⟩ := selected_bordered_kernel_disk d hcap
  obtain ⟨cp,H,ρp,hcp,hH,hρp,hρp1,hpb⟩ := selected_signed_product_disk d hcap
  obtain ⟨ca,A,ρa,hca,hA,hρa,_hρa1,hab⟩ := preferred_selected_continued_oneBody_profile d hcap
  let B := cappedCanonicalPreferredBump d cap hcap
  obtain ⟨J,hJ,hjac⟩ := preferred_contour_determinant_bound d B
  let c := min cp (min ca ck)
  let ρ := min ρp (min ρa ρk)
  have hc : 0<c := lt_min hcp (lt_min hca hck)
  have hρ : 0<ρ := lt_min hρp (lt_min hρa hρk)
  have hρp' : ρ≤ρp := min_le_left _ _
  have hρa' : ρ≤ρa := (min_le_right _ _).trans (min_le_left _ _)
  have hρk' : ρ≤ρk := (min_le_right _ _).trans (min_le_right _ _)
  have hcp' : c≤cp := min_le_left _ _
  have hca' : c≤ca := (min_le_right _ _).trans (min_le_left _ _)
  have hck' : c≤ck := (min_le_right _ _).trans (min_le_right _ _)
  have hρ1 : ρ≤1 := hρp'.trans hρp1
  refine ⟨c,H,A,J,ρ,hc,hH,hA,hJ,hρ,hρ1,?_⟩
  intro τ hτ hτρ
  obtain ⟨K,hK,hkb'⟩ := hkb τ hτ (hτρ.trans_le hρk')
  refine ⟨K,hK,?_⟩
  intro N hN ε hε hερ θ hw t ht σ hσ
  have hrad (c' : ℝ) (hcc : c≤c') :
      ‖t-IsingBulk.Branch.radialParameter d.alpha ε‖≤c'*τ^2/(N:ℝ)^3 :=
    ht.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcc (sq_nonneg _)) (by positivity))
  obtain ⟨hroot,hpair,hdet⟩ := hkb' N hN ε hε (hερ.trans_le hρk') θ hw t (hrad ck hck')
  obtain ⟨_hprod,hgap,hres⟩ := hpb N hN ε τ hε (hερ.trans_le hρp') hτ
    (hτρ.trans_le hρp') θ hw t (hrad cp hcp') σ hσ
  have hbody := hab N hN ε τ hε (hερ.trans_le hρa') hτ
    (hτρ.trans_le hρa') θ hw t (hrad ca hca')
  refine ⟨selectedContinuedDensity_analyticAt σ d B ε τ θ t hroot hpair hgap,?_⟩
  have hh := selectedContinuedDensity_norm σ d B ε τ θ t (pow_nonneg hJ.le _)
    (by positivity : 0≤H*(N:ℝ)/τ) (by positivity : 0≤(K*Real.sqrt (N+1))^(N+1))
    (hjac N hN τ hτ.le (hτρ.le.trans hρ1) θ) hres hdet (fun i => (hbody i).2)
  exact hh.trans_eq (by ring)

end
end IsingBulk.HT22.Selected
