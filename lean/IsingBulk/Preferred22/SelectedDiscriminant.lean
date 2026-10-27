import IsingBulk.Preferred22.SelectedRegularGap
import IsingBulk.Preferred22.SelectedOneBody

/-! The actual selected population has a uniform inverse-particle
lower bound for every dispersion discriminant, combining genuine true
branches with the regular angular complement. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set
set_option maxHeartbeats 800000

theorem preferred_selected_actual_discriminant (d : PreferredBranchData)
    {cap : ℝ} (hcap : 0<cap) :
    ∃ c ρ : ℝ,0<c ∧ 0<ρ ∧ ρ≤1 ∧ ∀ N : ℕ,0<N →
      ∀ ε τ : ℝ,0<ε → ε<ρ → 0<τ → τ<ρ → ∀ θ : Fin N → ℝ,
      (∀ i,θ i∈Icc (-Real.pi) Real.pi) →
      preferredFullPopulationWeight preferredPopulationCutoff
        (cappedCanonicalPreferredBump d cap hcap).p
        (cappedCanonicalPreferredBump d cap hcap).m θ≠0 →
      ∀ i : Fin N,c*τ/(N:ℝ)≤
        ‖(preferredRadialTrace d ε-Complex.cos
          (deformedAngles τ (cappedCanonicalPreferredBump d cap hcap).p
            (cappedCanonicalPreferredBump d cap hcap).m θ i))^2-1‖ := by
  let B := cappedCanonicalPreferredBump d cap hcap
  obtain ⟨γ,hγ,hmargin⟩ := cappedCanonicalPreferredBump_sine_margin d hcap
  obtain ⟨g,ρ₀,hg,hρ₀,hreg⟩ := preferred_selected_regular_source_gap d B
  let c := min g (γ/4)
  let ρ := min 1 ρ₀
  have hc : 0<c := lt_min hg (by positivity)
  have hρ : 0<ρ := lt_min zero_lt_one hρ₀
  have hρ1 : ρ≤1 := min_le_left _ _
  have hρr : ρ≤ρ₀ := min_le_right _ _
  refine ⟨c,ρ,hc,hρ,hρ1,?_⟩
  intro N hN ε τ hε hερ hτ hτρ θ hθ hw i
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hN1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hτ1 : τ≤1 := hτρ.le.trans hρ1
  let W := preferredRadialTrace d ε-Complex.cos (deformedAngles τ B.p B.m θ i)
  change c*τ/(N:ℝ)≤‖W^2-1‖
  by_cases hi : B.p (θ i)=1 ∨ B.m (θ i)=1
  · have hm := preferred_selected_plateau_margin d B hγ.le hmargin hε.le hτ.le θ hw i hi
    have hp : 0<W.im := (by positivity : 0<γ*τ/(4*(N:ℝ))).trans_le hm
    calc
      c*τ/(N:ℝ) ≤ (γ/4)*τ/(N:ℝ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_right _ _) hτ.le) hNr.le
      _ = γ*τ/(4*(N:ℝ)) := by ring
      _ ≤ W.im := hm
      _ ≤ ‖W^2-1‖ := preferred_upper_discriminant_margin hp.le
  · replace hi : B.p (θ i)≠1 ∧ B.m (θ i)≠1 := not_or.mp hi
    have hregular := preferred_selected_nonplateau_regular B (hθ i) hi.1 hi.2
    obtain ⟨hP,hQ⟩ := actual_occupancy_box hN B θ
    have hh := hreg ε τ (occupancy B.p θ/(N:ℝ)) (occupancy B.m θ/(N:ℝ)) (θ i)
      (by simpa only [abs_of_pos hε] using hερ.trans_le hρr)
      (by simpa only [abs_of_pos hτ] using hτρ.trans_le hρr) hP hQ hregular
    rw [←actual_bump_angle d B τ θ i] at hh
    have hct : c*τ/(N:ℝ)≤c := by
      apply (div_le_iff₀ hNr).mpr
      nlinarith [mul_le_mul_of_nonneg_left hτ1 hc.le,
        mul_le_mul_of_nonneg_left hN1 hc.le]
    exact (hct.trans (min_le_left _ _)).trans hh

end
end IsingBulk.Preferred22
