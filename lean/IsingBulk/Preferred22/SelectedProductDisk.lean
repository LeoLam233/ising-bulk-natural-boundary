import IsingBulk.Preferred22.SelectedRelativeDisk

/-! Whole-product gap and resolvent control on the genuine selected
continuation disk, obtained from the exact center attenuation and actual
relative movement of every root. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1000000

lemma preferred_finite_product_relative_bound {N : ℕ} (z w : Fin N → ℂ)
    (hz : ∀ i,z i≠0) {η : ℝ} (hrel : ∀ i,‖w i/z i-1‖≤η) :
    ‖∏ i,w i‖≤‖∏ i,z i‖*Real.exp ((N:ℝ)*η) := by
  have hpoint (i : Fin N) : ‖w i‖≤‖z i‖*Real.exp η := by
    have h := norm_sub_norm_le (w i/z i) (1:ℂ)
    simp only [norm_one] at h
    have hr : ‖w i/z i‖≤Real.exp η := by linarith [hrel i,Real.add_one_le_exp η]
    have he : w i=z i*(w i/z i) := by field_simp [hz i]
    rw [he,norm_mul]
    exact mul_le_mul_of_nonneg_left hr (norm_nonneg _)
  rw [norm_prod,norm_prod]
  calc
    _ ≤ ∏ i,‖z i‖*Real.exp η := Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hpoint i)
    _ = _ := by simp [Finset.prod_mul_distrib,Real.exp_nat_mul]

def preferredSelectedContinuedProduct {N : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (ε τ : ℝ) (θ : Fin N → ℝ) (t : ℂ) : ℂ :=
  ∏ i,preferredSelectedContinuedRoot d B ε τ θ i t

/-- The physical product gap survives throughout a common N^(-3)
parameter disk. For fixed positive tau the radius is exactly c_tau/N^3.
No whole-product continuation or denominator bound is assumed. -/
theorem preferred_selected_continued_product_disk (d : PreferredBranchData)
    {cap : ℝ} (hcap : 0<cap) :
    ∃ c C ρ : ℝ,0<c ∧ 0<C ∧ 0<ρ ∧ ρ≤1 ∧ ∀ N : ℕ,0<N →
      ∀ ε τ : ℝ,0<ε → ε<ρ → 0<τ → τ<ρ → ∀ θ : Fin N → ℝ,
      preferredFullPopulationWeight preferredPopulationCutoff
        (cappedCanonicalPreferredBump d cap hcap).p
        (cappedCanonicalPreferredBump d cap hcap).m θ≠0 →
      ∀ t : ℂ,‖t-IsingBulk.Branch.radialParameter d.alpha ε‖≤c*τ^2/(N:ℝ)^3 →
      AnalyticAt ℂ (preferredSelectedContinuedProduct d
        (cappedCanonicalPreferredBump d cap hcap) ε τ θ) t ∧
      ‖preferredSelectedContinuedProduct d (cappedCanonicalPreferredBump d cap hcap) ε τ θ t‖≤
        Real.exp (-(c*τ/(N:ℝ))) ∧
      ‖(1+preferredSelectedContinuedProduct d (cappedCanonicalPreferredBump d cap hcap) ε τ θ t)/
        (1-preferredSelectedContinuedProduct d (cappedCanonicalPreferredBump d cap hcap) ε τ θ t)‖≤
        C*(N:ℝ)/τ := by
  obtain ⟨g₀,hg₀,hphase⟩ := preferred_selected_attenuation_gap d hcap
  let g := min 1 g₀
  have hg : 0<g := lt_min zero_lt_one hg₀
  have hg1 : g≤1 := min_le_left _ _
  have hgg : g≤g₀ := min_le_right _ _
  obtain ⟨cr,ρ,hcr,hρ,hρ1,hrelative⟩ := preferred_selected_root_relative_disk d hcap
    (by positivity : 0<g/2)
  let c := min cr (g/2)
  have hc : 0<c := lt_min hcr (by positivity)
  have hcc : c≤cr := min_le_left _ _
  have hcg : c≤g/2 := min_le_right _ _
  have hc1 : c≤1 := by linarith
  refine ⟨c,2*Real.exp 1/c,ρ,hc,by positivity,hρ,hρ1,?_⟩
  intro N hN ε τ hε hερ hτ hτρ θ hw t ht
  let B := cappedCanonicalPreferredBump d cap hcap
  let z := fun i : Fin N => physicalRoot (preferredRadialTrace d ε-
    Complex.cos (deformedAngles τ B.p B.m θ i))
  let w := fun i : Fin N => preferredSelectedContinuedRoot d B ε τ θ i t
  let η := (g/2)*τ/(N:ℝ)^2
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hN1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hτ1 : τ≤1 := hτρ.le.trans hρ1
  have hε1 : ε≤1 := hερ.le.trans hρ1
  have ht' : ‖t-IsingBulk.Branch.radialParameter d.alpha ε‖≤cr*τ^2/(N:ℝ)^3 :=
    ht.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcc (sq_nonneg _)) (by positivity))
  have hrel := hrelative N hN ε τ hε hερ hτ hτρ θ hw t ht'
  have ha : AnalyticAt ℂ (preferredSelectedContinuedProduct d B ε τ θ) t :=
    Finset.univ.analyticAt_fun_prod (fun i _ => (hrel i).1)
  have hprod := preferred_finite_product_relative_bound z w
    (fun i => physicalRoot_ne_zero _) (fun i => (hrel i).2)
  have hcenter : ‖∏ i,z i‖≤Real.exp (-(g*τ/(N:ℝ))) := by
    change ‖preferredActualZ d B ε τ θ‖≤_
    rw [preferredActualZ_eq_exp d B hε hτ.le θ,Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hp := hphase N hN ε τ hε hε1 hτ.le hτ1 θ hw
    have hg' := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hgg hτ.le) hNr.le
    simp only [Complex.mul_re,Complex.neg_re,Complex.neg_im,Complex.I_re,
      Complex.I_im,neg_zero,zero_mul,neg_neg,zero_sub,neg_one_mul]
    linarith
  have hwhole : ‖preferredSelectedContinuedProduct d B ε τ θ t‖≤Real.exp (-(c*τ/(N:ℝ))) := by
    change ‖∏ i,w i‖≤_
    calc
      _ ≤ ‖∏ i,z i‖*Real.exp ((N:ℝ)*η) := hprod
      _ ≤ Real.exp (-(g*τ/(N:ℝ)))*Real.exp ((N:ℝ)*η) :=
        mul_le_mul_of_nonneg_right hcenter (Real.exp_pos _).le
      _ = Real.exp (-((g/2)*τ/(N:ℝ))) := by
        rw [←Real.exp_add]
        congr 1
        dsimp only [η]
        field_simp
        norm_num
      _ ≤ Real.exp (-(c*τ/(N:ℝ))) := by
        apply Real.exp_le_exp.mpr
        exact neg_le_neg (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcg hτ.le) hNr.le)
  refine ⟨ha,hwhole,?_⟩
  have hx : 0<c*τ/(N:ℝ) := by positivity
  have hx1 : c*τ/(N:ℝ)≤1 := by
    apply (div_le_one₀ hNr).mpr
    have h := mul_le_mul hc1 hτ1 hτ.le (by norm_num : (0:ℝ)≤1)
    nlinarith
  calc
    _ ≤ 2*Real.exp 1/(c*τ/(N:ℝ)) := preferred_resolvent_of_attenuation hx hx1 hwhole
    _ = (2*Real.exp 1/c)*(N:ℝ)/τ := by field_simp

end
end IsingBulk.Preferred22
