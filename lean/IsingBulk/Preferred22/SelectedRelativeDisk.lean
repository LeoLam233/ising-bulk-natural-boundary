import IsingBulk.Preferred22.SelectedContinuation
import IsingBulk.Preferred22.RootMovement

/-! A uniform relative-root perturbation bound at the exact N^(-3)
selected parameter scale, retaining the same actual real angular weights. -/
namespace IsingBulk.Preferred22
noncomputable section
set_option maxHeartbeats 1400000

theorem preferred_selected_root_relative_disk (d : PreferredBranchData)
    {cap a : ℝ} (hcap : 0<cap) (ha : 0<a) :
    ∃ c ρ : ℝ,0<c ∧ 0<ρ ∧ ρ≤1 ∧ ∀ N : ℕ,0<N →
      ∀ ε τ : ℝ,0<ε → ε<ρ → 0<τ → τ<ρ → ∀ θ : Fin N → ℝ,
      preferredFullPopulationWeight preferredPopulationCutoff
        (cappedCanonicalPreferredBump d cap hcap).p
        (cappedCanonicalPreferredBump d cap hcap).m θ≠0 →
      ∀ t : ℂ,‖t-IsingBulk.Branch.radialParameter d.alpha ε‖≤c*τ^2/(N:ℝ)^3 →
      ∀ i : Fin N,
        AnalyticAt ℂ (preferredSelectedContinuedRoot d
          (cappedCanonicalPreferredBump d cap hcap) ε τ θ i) t ∧
        ‖preferredSelectedContinuedRoot d (cappedCanonicalPreferredBump d cap hcap) ε τ θ i t /
          physicalRoot (preferredRadialTrace d ε-Complex.cos
            (deformedAngles τ (cappedCanonicalPreferredBump d cap hcap).p
              (cappedCanonicalPreferredBump d cap hcap).m θ i))-1‖≤a*τ/(N:ℝ)^2 := by
  obtain ⟨g₀,ρg,hg₀,hρg,hρg1,hgap⟩ := preferred_selected_discriminant_all_angles d hcap
  obtain ⟨cb,ρb,hcb,hρb,_hρb1,hbranch⟩ := preferred_selected_complete_branch_disk d hcap
  let B := cappedCanonicalPreferredBump d cap hcap
  let g := min 1 g₀
  let R := 3+Real.exp 1
  let C := (2*R+1)*(2*R+2)
  have hg : 0<g := lt_min zero_lt_one hg₀
  have hg1 : g≤1 := min_le_left _ _
  have hgg : g≤g₀ := min_le_right _ _
  have hR : 0<R := by dsimp only [R]; positivity
  have hC : 0<C := by dsimp only [C]; positivity
  have hgs : 0<Real.sqrt g := Real.sqrt_pos.mpr hg
  let c := min cb (min (1/4:ℝ) (a*Real.sqrt g/(3*C)))
  let ρ := min ρg ρb
  have hc : 0<c := lt_min hcb (lt_min (by norm_num) (by positivity))
  have hρ : 0<ρ := lt_min hρg hρb
  have hρ1 : ρ≤1 := (min_le_left _ _).trans hρg1
  have hcc : c≤cb := min_le_left _ _
  have hc4 : c≤1/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hca : c≤a*Real.sqrt g/(3*C) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨c,ρ,hc,hρ,hρ1,?_⟩
  intro N hN ε τ hε hερ hτ hτρ θ hw t ht i
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  let w := deformedAngles τ B.p B.m θ i
  let W := preferredRadialTrace d ε-Complex.cos w
  let V := temperatureTrace t-Complex.cos w
  let D := g*τ/(N:ℝ)
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hN1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hτ1 : τ≤1 := hτρ.le.trans hρ1
  have hε1 : ε≤1 := hερ.le.trans hρ1
  have hτsq : τ^2≤τ := by nlinarith
  have hradBranch : ‖t-s‖≤cb*τ/(N:ℝ)^3 := by
    exact ht.trans (div_le_div_of_nonneg_right
      (mul_le_mul hcc hτsq (sq_nonneg _) hcb.le) (by positivity))
  have hbranch' := (hbranch N hN ε τ hε (hερ.trans_le (min_le_right _ _))
    hτ (hτρ.trans_le (min_le_right _ _)) θ hw t hradBranch i).1
  refine ⟨hbranch',?_⟩
  have hpow : (N:ℝ)≤(N:ℝ)^3 := by
    have hs : 1≤(N:ℝ)^2 := one_le_pow₀ hN1
    nlinarith [mul_le_mul_of_nonneg_left hs hNr.le]
  have hrad : ‖t-s‖≤c*τ/(N:ℝ) := ht.trans
    ((div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hτsq hc.le) (by positivity)).trans
      (div_le_div_of_nonneg_left (mul_nonneg hc.le hτ.le) hNr hpow))
  have hrad1 : c*τ/(N:ℝ)≤1/4 := by
    apply (div_le_iff₀ hNr).mpr
    nlinarith [mul_le_mul_of_nonneg_left hτ1 hc.le]
  have hs : 1≤‖s‖ := by
    have he : ‖s‖=1+ε := by
      simp only [s,IsingBulk.Branch.radialParameter,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        Complex.norm_exp_ofReal_mul_I,abs_of_nonneg (by positivity : 0≤1+ε),mul_one]
    rw [he]
    linarith
  have htNorm : (1:ℝ)/2≤‖t‖ := by
    have hn := norm_sub_norm_le s t
    rw [norm_sub_rev s t] at hn
    linarith [hrad.trans hrad1]
  have hVW : ‖V-W‖≤3*‖t-s‖ := by
    have he : V-W=temperatureTrace t-temperatureTrace s := by
      dsimp only [V,W,s,preferredRadialTrace,temperatureTrace]
      ring
    rw [he]
    exact preferred_temperatureTrace_lipschitz hs htNorm
  have hsmall : ‖V-W‖≤1 := by linarith [hrad.trans hrad1]
  have hWnorm : ‖W‖≤R :=
    (norm_sub_le _ _).trans (add_le_add (preferredRadialTrace_norm_bound d hε.le hε1)
      (preferred_cos_norm_le_exp_one ((preferred_deformedAngles_im_bound hN d B hτ.le θ i).trans hτ1)))
  have hsin : 0<Real.sin d.alpha := Real.sin_pos_of_pos_of_lt_pi d.alpha_pos
    (by linarith [d.alpha_lt,Real.pi_pos])
  have hoff : OffRealSegment W := Or.inl (ne_of_gt
    ((mul_pos hε hsin).trans_le (preferredActualW_im_lower d B hε.le hτ.le θ i)))
  have hD : 0<D := by dsimp only [D]; positivity
  have hD1 : D≤1 := by
    apply (div_le_one₀ hNr).mpr
    have h := mul_le_mul hg1 hτ1 hτ.le (by norm_num : (0:ℝ)≤1)
    nlinarith
  have hgapD : D≤‖W^2-1‖ :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hgg hτ.le) hNr.le).trans
      (hgap N hN ε τ hε (hερ.trans_le (min_le_left _ _)) hτ
        (hτρ.trans_le (min_le_left _ _)) θ hw i)
  have hx : 0<τ/(N:ℝ) := div_pos hτ hNr
  have hx1 : τ/(N:ℝ)≤1 := (div_le_one₀ hNr).mpr (hτ1.trans hN1)
  have hden : Real.sqrt g*(τ/(N:ℝ))≤Real.sqrt D := by
    apply (Real.le_sqrt (by positivity) hD.le).mpr
    rw [mul_pow,Real.sq_sqrt hg.le]
    calc
      g*(τ/(N:ℝ))^2 ≤ g*(τ/(N:ℝ)) :=
        mul_le_mul_of_nonneg_left (by nlinarith : (τ/(N:ℝ))^2≤τ/(N:ℝ)) hg.le
      _ = D := by dsimp only [D]; ring
  have hcoef : 3*C*c/Real.sqrt g≤a := by
    apply (div_le_iff₀ hgs).mpr
    have h := (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<3) hC)).mp hca
    nlinarith
  have hmove := preferred_local_root_relative_bound hR.le hoff hWnorm hD hD1 hgapD hsmall
  change ‖localPhysicalRoot W V/physicalRoot W-1‖≤a*τ/(N:ℝ)^2
  calc
    _ ≤ C*‖V-W‖/Real.sqrt D := hmove
    _ ≤ C*(3*‖t-s‖)/Real.sqrt D :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hVW hC.le) (Real.sqrt_nonneg _)
    _ ≤ C*(3*(c*τ^2/(N:ℝ)^3))/Real.sqrt D :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht (by norm_num)) hC.le)
        (Real.sqrt_nonneg _)
    _ ≤ C*(3*(c*τ^2/(N:ℝ)^3))/(Real.sqrt g*(τ/(N:ℝ))) :=
      div_le_div_of_nonneg_left (by positivity) (mul_pos hgs hx) hden
    _ = (3*C*c/Real.sqrt g)*(τ/(N:ℝ)^2) := by field_simp
    _ ≤ a*(τ/(N:ℝ)^2) := mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = _ := by ring

end
end IsingBulk.Preferred22
