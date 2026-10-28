import IsingBulk.HT22.Selected.PhysicalGerm
import IsingBulk.HT22.Selected.WeightedJets
import IsingBulk.First.DominatedAnalyticIntegral

/-! Cauchy estimates of the actual selected integrand integrate to estimates
of the exact complex derivatives of the complete selected population term. -/
namespace IsingBulk.HT22.Selected
open IsingBulk.Preferred22
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology
set_option maxHeartbeats 1300000

def selectedIntegral (negative : Bool) (n : ℕ) (τ : ℝ) (p m : ℝ → ℝ) (t : ℂ) : ℂ :=
  Physical.weightedContourIntegral negative n τ p m
    (preferredFullPopulationWeight preferredPopulationCutoff p m) t

lemma selected_weight_norm_le_one {N : ℕ} (p m : ℝ → ℝ) (θ : Fin N → ℝ) :
    ‖(preferredFullPopulationWeight preferredPopulationCutoff p m θ:ℂ)‖≤1 := by
  obtain ⟨hp0,hp1⟩ := preferredPopulationCutoff_bounds (occupancy p θ)
  obtain ⟨hm0,hm1⟩ := preferredPopulationCutoff_bounds (occupancy m θ)
  rw [Complex.norm_real,Real.norm_eq_abs,preferredFullPopulationWeight,fullWeight,
    abs_of_nonneg (mul_nonneg hp0 hm0)]
  nlinarith [mul_le_mul hp1 hm1 hm0 (by norm_num : (0:ℝ)≤1)]

theorem selected_derivative_from_pointwise_disk (negative : Bool) (n : ℕ)
    (d : PreferredBranchData) (B : PreferredCoareaBump d)
    {ε τ R M : ℝ} (hε : 0<ε) (hτ : 0≤τ) (hR : 0<R) (hM : 0≤M) (j : ℕ)
    (hpoint : ∀ θ : Fin (2*n+1) → ℝ,
      preferredFullPopulationWeight preferredPopulationCutoff B.p B.m θ≠0 →
      AnalyticOnNhd ℂ (selectedContinuedDensity (Physical.constraintSign negative) d B ε τ θ)
        (Metric.closedBall (IsingBulk.Branch.radialParameter d.alpha ε) R) ∧
      ∀ t∈Metric.closedBall (IsingBulk.Branch.radialParameter d.alpha ε) R,
        ‖selectedContinuedDensity (Physical.constraintSign negative) d B ε τ θ t‖≤
          M*(∏ i,preferredSelectedOneBodyProfile d ε (θ i))) :
    ‖iteratedDeriv j (selectedIntegral negative (2*n) τ B.p B.m)
      (IsingBulk.Branch.radialParameter d.alpha ε)‖≤
      ((j.factorial:ℝ)*M/R^j)*
        (∫ θ in angularBox (2*n),∏ i : Fin (2*n+1),
          preferredSelectedOneBodyProfile d ε (Physical.constrainedAngles negative (2*n) θ i)) := by
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  let w := fun θ : Fin (2*n+1) → ℝ =>
    (preferredFullPopulationWeight preferredPopulationCutoff B.p B.m θ:ℂ)
  let f := fun θ : Fin (2*n) → ℝ => ∏ i : Fin (2*n+1),
    preferredSelectedOneBodyProfile d ε (Physical.constrainedAngles negative (2*n) θ i)
  have hw : Continuous w := by
    have hp := B.smooth.continuous
    have hm := B.m_smooth.continuous
    have hη := preferredPopulationCutoff_smooth.continuous
    unfold w preferredFullPopulationWeight fullWeight occupancy
    fun_prop
  have hS : 0<(temperatureTrace s).im := preferredRadialTrace_im_pos d hε
  obtain ⟨heq,hint⟩ := signed_weighted_contour_integral_jets negative (2*n) d B hτ w hw hS j
  change iteratedDeriv j (selectedIntegral negative (2*n) τ B.p B.m) s = _ at heq
  let G := fun θ : Fin (2*n) → ℝ => iteratedDeriv j (fun t : ℂ =>
    w (Physical.constrainedAngles negative (2*n) θ)*Physical.bareContourDensity negative τ B.p B.m t (Physical.constrainedAngles negative (2*n) θ)) s
  have hG (θ : Fin (2*n) → ℝ) : ‖G θ‖≤((j.factorial:ℝ)*M/R^j)*f θ := by
    let x := Physical.constrainedAngles negative (2*n) θ
    by_cases hx : preferredFullPopulationWeight preferredPopulationCutoff B.p B.m x=0
    · have hwx : w x=0 := by simp [w,hx]
      have hzero : G θ=0 := by
        change iteratedDeriv j (fun t : ℂ => w x*Physical.bareContourDensity negative τ B.p B.m t x) s=0
        simp only [hwx,zero_mul,iteratedDeriv_fun_const_zero]
      rw [hzero,norm_zero]
      exact mul_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg _) hM) (pow_nonneg hR.le _))
        (Finset.prod_nonneg (fun i _ => (preferred_selected_oneBody_profile_pos d hε _).le))
    · obtain ⟨ha,hbound⟩ := hpoint x hx
      have hb := IsingBulk.First.cauchy_bound_on_subdisk ha hbound hR (Subset.rfl) j
      have hgerm := selectedContinuedDensity_physical_germ negative n d B hε hτ x
      have hd : G θ=w x*iteratedDeriv j (selectedContinuedDensity (Physical.constraintSign negative) d B ε τ x) s := by
        dsimp only [G]
        rw [iteratedDeriv_const_mul_field,←hgerm.iteratedDeriv_eq]
      rw [hd,norm_mul]
      have hwx : ‖w x‖≤1 := selected_weight_norm_le_one B.p B.m x
      calc
        _ ≤ 1*‖iteratedDeriv j (selectedContinuedDensity (Physical.constraintSign negative) d B ε τ x) s‖ :=
          mul_le_mul_of_nonneg_right hwx (norm_nonneg _)
        _ ≤ (j.factorial:ℝ)*(M*f θ)/R^j := by simpa only [one_mul] using hb
        _ = _ := by ring
  have hf : Continuous f := by
    have hc := preferred_selected_oneBody_profile_continuous d hε
    have hx := Physical.constrainedAngles_continuous negative (2*n)
    unfold f
    fun_prop
  have hfi : IntegrableOn f (angularBox (2*n)) :=
    (hf.continuousOn.integrableOn_compact (isCompact_univ_pi (fun _ : Fin (2*n) => isCompact_Icc))).mono_set
      (Set.pi_mono fun _ _ => Ioc_subset_Icc_self)
  rw [heq]
  calc
    _ ≤ ∫ θ in angularBox (2*n),‖G θ‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ θ in angularBox (2*n),((j.factorial:ℝ)*M/R^j)*f θ :=
      integral_mono hint.norm (hfi.const_mul _) hG
    _ = _ := integral_const_mul _ _

end
end IsingBulk.HT22.Selected
