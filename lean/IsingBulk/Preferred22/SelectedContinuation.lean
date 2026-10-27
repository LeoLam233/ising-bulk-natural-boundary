import IsingBulk.Preferred22.SelectedPeriodic
import IsingBulk.Preferred22.RootContinuation

/-! The complete selected vector uses the explicit analytic continuation of
each center physical root on one uniform N^(-3) disk. Real population weights
and the real angular contour are fixed during this parameter continuation. -/
namespace IsingBulk.Preferred22
noncomputable section
open Filter Set
open scoped Topology
set_option maxHeartbeats 1200000

def preferredSelectedContinuedRoot {N : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (ε τ : ℝ) (θ : Fin N → ℝ) (i : Fin N) (t : ℂ) : ℂ :=
  localPhysicalRoot (preferredRadialTrace d ε-Complex.cos (deformedAngles τ B.p B.m θ i))
    (temperatureTrace t-Complex.cos (deformedAngles τ B.p B.m θ i))

lemma preferred_selected_continued_root_germ {N : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {ε τ : ℝ} (hε : 0<ε) (hτ : 0≤τ)
    (θ : Fin N → ℝ) (i : Fin N) :
    preferredSelectedContinuedRoot d B ε τ θ i =ᶠ[𝓝 (IsingBulk.Branch.radialParameter d.alpha ε)]
      (fun t : ℂ => physicalRoot (temperatureTrace t-Complex.cos (deformedAngles τ B.p B.m θ i))) := by
  have hsin : 0<Real.sin d.alpha := Real.sin_pos_of_pos_of_lt_pi d.alpha_pos
    (by linarith [d.alpha_lt,Real.pi_pos])
  have hW := (mul_pos hε hsin).trans_le (preferredActualW_im_lower d B hε.le hτ θ i)
  have hoff : OffRealSegment (preferredRadialTrace d ε-Complex.cos (deformedAngles τ B.p B.m θ i)) :=
    Or.inl (ne_of_gt hW)
  have hs0 : IsingBulk.Branch.radialParameter d.alpha ε≠0 := by
    simp only [IsingBulk.Branch.radialParameter,mul_ne_zero_iff,ne_eq,Complex.ofReal_eq_zero]
    exact ⟨by linarith,Complex.exp_ne_zero _⟩
  have hg : ContinuousAt (fun t : ℂ => temperatureTrace t-Complex.cos (deformedAngles τ B.p B.m θ i))
      (IsingBulk.Branch.radialParameter d.alpha ε) := by
    unfold temperatureTrace
    exact (continuousAt_id.add (continuousAt_id.inv₀ hs0)).sub continuousAt_const
  exact (preferred_local_root_germ hoff).comp_tendsto hg

/-- One fixed positive radius constant precedes every particle order and
all real angular configurations. The continued root is analytic on the disk
and every actual dispersion discriminant retains a c*tau/N margin there. -/
theorem preferred_selected_complete_branch_disk (d : PreferredBranchData)
    {cap : ℝ} (hcap : 0<cap) :
    ∃ c ρ : ℝ,0<c ∧ 0<ρ ∧ ρ≤1 ∧ ∀ N : ℕ,0<N →
      ∀ ε τ : ℝ,0<ε → ε<ρ → 0<τ → τ<ρ → ∀ θ : Fin N → ℝ,
      preferredFullPopulationWeight preferredPopulationCutoff
        (cappedCanonicalPreferredBump d cap hcap).p
        (cappedCanonicalPreferredBump d cap hcap).m θ≠0 →
      ∀ t : ℂ,‖t-IsingBulk.Branch.radialParameter d.alpha ε‖≤c*τ/(N:ℝ)^3 →
      ∀ i : Fin N,
        AnalyticAt ℂ (preferredSelectedContinuedRoot d
          (cappedCanonicalPreferredBump d cap hcap) ε τ θ i) t ∧
        c*τ/(N:ℝ)≤‖(temperatureTrace t-Complex.cos
          (deformedAngles τ (cappedCanonicalPreferredBump d cap hcap).p
            (cappedCanonicalPreferredBump d cap hcap).m θ i))^2-1‖ := by
  obtain ⟨g,ρ,hg,hρ,hρ1,hgap⟩ := preferred_selected_discriminant_all_angles d hcap
  let B := cappedCanonicalPreferredBump d cap hcap
  let R := 3+Real.exp 1
  have hR : 0<R := by dsimp only [R]; positivity
  have hR1 : 0<2*R+1 := by positivity
  let c := min (1/4:ℝ) (min (g/2) (g/(6*(2*R+1))))
  have hc : 0<c := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hc4 : c≤1/4 := min_le_left _ _
  have hcg : c≤g/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hcR : c≤g/(6*(2*R+1)) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨c,ρ,hc,hρ,hρ1,?_⟩
  intro N hN ε τ hε hερ hτ hτρ θ hw t ht i
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  let w := deformedAngles τ B.p B.m θ i
  let W := preferredRadialTrace d ε-Complex.cos w
  let V := temperatureTrace t-Complex.cos w
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hN1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hτ1 : τ≤1 := hτρ.le.trans hρ1
  have hε1 : ε≤1 := hερ.le.trans hρ1
  have hpow : (N:ℝ)≤(N:ℝ)^3 := by
    have hs : 1≤(N:ℝ)^2 := one_le_pow₀ hN1
    nlinarith [mul_le_mul_of_nonneg_left hs hNr.le]
  have hrad : ‖t-s‖≤c*τ/(N:ℝ) :=
    ht.trans (div_le_div_of_nonneg_left (mul_nonneg hc.le hτ.le) hNr hpow)
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
  have ht0 : t≠0 := by intro h; norm_num [h] at htNorm
  have hWnorm : ‖W‖≤R := by
    exact (norm_sub_le _ _).trans (add_le_add (preferredRadialTrace_norm_bound d hε.le hε1)
      (preferred_cos_norm_le_exp_one ((preferred_deformedAngles_im_bound hN d B hτ.le θ i).trans hτ1)))
  have hgapW : g*τ/(N:ℝ)≤‖W^2-1‖ := hgap N hN ε τ hε hερ hτ hτρ θ hw i
  have hD : W^2-1≠0 := norm_pos_iff.mp ((by positivity : 0<g*τ/(N:ℝ)).trans_le hgapW)
  have hVW : ‖V-W‖≤3*‖t-s‖ := by
    have he : V-W=temperatureTrace t-temperatureTrace s := by
      dsimp only [V,W,s,preferredRadialTrace,temperatureTrace]
      ring
    rw [he]
    exact preferred_temperatureTrace_lipschitz hs htNorm
  have hsmall : ‖V-W‖≤1 := by linarith [hrad.trans hrad1]
  have hc3 : 3*c≤g/(2*(2*R+1)) := by
    apply (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) hR1)).mpr
    have h := (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<6) hR1)).mp hcR
    nlinarith
  have hdelta : ‖V-W‖≤‖W^2-1‖/(2*(2*R+1)) := by
    calc
      _ ≤ 3*(c*τ/(N:ℝ)) := hVW.trans (mul_le_mul_of_nonneg_left hrad (by norm_num))
      _ = (3*c)*(τ/(N:ℝ)) := by ring
      _ ≤ (g/(2*(2*R+1)))*(τ/(N:ℝ)) :=
        mul_le_mul_of_nonneg_right hc3 (div_nonneg hτ.le hNr.le)
      _ = (g*τ/(N:ℝ))/(2*(2*R+1)) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hgapW (by positivity)
  obtain ⟨_,_,hdisc,ha⟩ := preferred_discriminant_ratio_disk hR.le hWnorm hD hsmall hdelta
  have hinner : AnalyticAt ℂ (fun z : ℂ => temperatureTrace z-Complex.cos w) t :=
    (analyticAt_id.add (analyticAt_id.inv ht0)).sub analyticAt_const
  refine ⟨ha.comp (f := fun z : ℂ => temperatureTrace z-Complex.cos w) hinner,?_⟩
  calc
    c*τ/(N:ℝ) ≤ (g/2)*τ/(N:ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcg hτ.le) hNr.le
    _ = (g*τ/(N:ℝ))/2 := by ring
    _ ≤ ‖W^2-1‖/2 := div_le_div_of_nonneg_right hgapW (by norm_num)
    _ ≤ ‖V^2-1‖ := hdisc

end
end IsingBulk.Preferred22
