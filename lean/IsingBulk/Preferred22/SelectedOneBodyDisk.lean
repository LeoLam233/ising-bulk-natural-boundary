import IsingBulk.Preferred22.SelectedOneBodyMajorant
import IsingBulk.Preferred22.SelectedRelativeDisk
import IsingBulk.Preferred22.RootOneBodyMovement

/-! The independent actual one-body majorant persists on the entire
selected N^(-3) complex parameter disk, on the legal continued sheet. -/
namespace IsingBulk.Preferred22
noncomputable section
set_option maxHeartbeats 1300000

theorem preferred_selected_continued_oneBody_profile (d : PreferredBranchData)
    {cap : ℝ} (hcap : 0<cap) :
    ∃ c C ρ : ℝ,0<c ∧ 0<C ∧ 0<ρ ∧ ρ≤1 ∧ ∀ N : ℕ,0<N →
      ∀ ε τ : ℝ,0<ε → ε<ρ → 0<τ → τ<ρ → ∀ θ : Fin N → ℝ,
      preferredFullPopulationWeight preferredPopulationCutoff
        (cappedCanonicalPreferredBump d cap hcap).p
        (cappedCanonicalPreferredBump d cap hcap).m θ≠0 →
      ∀ t : ℂ,‖t-IsingBulk.Branch.radialParameter d.alpha ε‖≤c*τ^2/(N:ℝ)^3 →
      ∀ i : Fin N,
      AnalyticAt ℂ (fun z => oneBody (preferredSelectedContinuedRoot d
        (cappedCanonicalPreferredBump d cap hcap) ε τ θ i z)) t ∧
      ‖oneBody (preferredSelectedContinuedRoot d
        (cappedCanonicalPreferredBump d cap hcap) ε τ θ i t)‖≤
        C*preferredSelectedOneBodyProfile d ε (θ i) := by
  let B := cappedCanonicalPreferredBump d cap hcap
  obtain ⟨A,ρa,hA,hρa,_hρa1,hprofile⟩ := preferred_actual_oneBody_profile d B
  obtain ⟨g,ρg,hg,hρg,hρg1,hgap⟩ := preferred_selected_discriminant_all_angles d hcap
  let a := min 1 (Real.sqrt g/3)
  have ha : 0<a := lt_min zero_lt_one (by positivity)
  have ha1 : a≤1 := min_le_left _ _
  have hag : a≤Real.sqrt g/3 := min_le_right _ _
  obtain ⟨c,ρr,hc,hρr,_hρr1,hrelative⟩ := preferred_selected_root_relative_disk d hcap ha
  let ρ := min ρa (min ρg ρr)
  have hρ : 0<ρ := lt_min hρa (lt_min hρg hρr)
  have hρg' : ρ≤ρg := (min_le_right _ _).trans (min_le_left _ _)
  have hρr' : ρ≤ρr := (min_le_right _ _).trans (min_le_right _ _)
  have hρ1 : ρ≤1 := hρg'.trans hρg1
  refine ⟨c,4*A,ρ,hc,by positivity,hρ,hρ1,?_⟩
  intro N hN ε τ hε hερ hτ hτρ θ hw t ht i
  let W := preferredRadialTrace d ε-Complex.cos (deformedAngles τ B.p B.m θ i)
  let w := preferredSelectedContinuedRoot d B ε τ θ i t
  let D := g*τ/(N:ℝ)
  let η := a*τ/(N:ℝ)^2
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hN1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hτ1 : τ≤1 := (hτρ.trans_le hρ1).le
  have hN2 : (N:ℝ)≤(N:ℝ)^2 := by nlinarith
  have hrelative' := hrelative N hN ε τ hε (hερ.trans_le hρr') hτ
    (hτρ.trans_le hρr') θ hw t ht i
  have hD : 0<D := by dsimp only [D]; positivity
  have hη : 0≤η := by dsimp only [η]; positivity
  have hηa : η≤a*(τ/(N:ℝ)) := by
    dsimp only [η]
    calc
      _ ≤ a*τ/(N:ℝ) := div_le_div_of_nonneg_left (mul_nonneg ha.le hτ.le) hNr hN2
      _ = _ := by ring
  have hx : 0≤τ/(N:ℝ) := by positivity
  have hx1 : τ/(N:ℝ)≤1 := (div_le_one₀ hNr).mpr (hτ1.trans hN1)
  have hη1 : η≤1 := by
    have hh := mul_le_mul ha1 hx1 hx (by norm_num : (0:ℝ)≤1)
    nlinarith
  have hsD : Real.sqrt g*(τ/(N:ℝ))≤Real.sqrt D := by
    apply (Real.le_sqrt (by positivity) hD.le).mpr
    rw [mul_pow,Real.sq_sqrt hg.le]
    calc
      g*(τ/(N:ℝ))^2 ≤ g*(τ/(N:ℝ)) :=
        mul_le_mul_of_nonneg_left (by nlinarith : (τ/(N:ℝ))^2≤τ/(N:ℝ)) hg.le
      _ = D := by dsimp only [D]; ring
  have hsmall : 3*η≤Real.sqrt D := by
    have hh := mul_le_mul_of_nonneg_right (show 3*a≤Real.sqrt g by linarith) hx
    nlinarith
  have hsin : 0<Real.sin d.alpha := Real.sin_pos_of_pos_of_lt_pi d.alpha_pos
    (by linarith [d.alpha_lt,Real.pi_pos])
  have hW : OffRealSegment W := Or.inl (ne_of_gt
    ((mul_pos hε hsin).trans_le (preferredActualW_im_lower d B hε.le hτ.le θ i)))
  have hgapD : D≤‖W^2-1‖ := hgap N hN ε τ hε (hερ.trans_le hρg') hτ
    (hτρ.trans_le hρg') θ hw i
  obtain ⟨hden,hnorm⟩ := preferred_oneBody_relative_movement hW hD hgapD hη hη1 hsmall hrelative'.2
  have han : AnalyticAt ℂ (fun z => oneBody (preferredSelectedContinuedRoot d B ε τ θ i z)) t := by
    exact (analyticAt_const.mul hrelative'.1).div
      (analyticAt_const.sub (hrelative'.1.pow 2)) hden
  refine ⟨han,?_⟩
  have hb := hprofile N hN ε τ hε (hερ.trans_le (min_le_left _ _)) hτ.le
    (hτρ.trans_le (min_le_left _ _)) θ i
  calc
    ‖oneBody w‖ ≤ 4*‖oneBody (physicalRoot W)‖ := hnorm
    _ ≤ 4*(A*preferredSelectedOneBodyProfile d ε (θ i)) :=
      mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = _ := by ring

end
end IsingBulk.Preferred22
