import IsingBulk.Anisotropic.RegularEdges.PositiveEndpointHigh

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open Set Filter Metric FormFactors RegularEdges
open scoped Topology
set_option maxHeartbeats 800000

/-- Actual normalized physical fourth-root branch pulled into the paper chart,
with agreement on an open domain containing the entire sufficiently short
inward ray. The branch is derived from the physical normalization. -/
theorem exists_paper_physical_prefactor {lam : ℝ} (hlam : 0<lam)
    {Z f : ℂ → ℂ} {r : ℝ} (hr : 0<r)
    (hZ : AnalyticOnNhd ℂ Z (ball 0 r))
    (hd : spectralDet lam (Z 0)≠0) (hu : |spectralU lam (Z 0)|<1)
    (hmap : MapsTo Z (upperBall r) (omegaH lam))
    (hf : AnalyticAt ℂ f 0) (hf0 : f 0=0)
    (hin : ∀ᶠ ε : ℝ in 𝓝[>] 0, f (-(ε:ℂ))∈upperBall r) :
    ∃ (D : Set ℂ) (b : ℂ → ℂ), IsOpen D ∧ AnalyticAt ℂ b 0 ∧ b 0≠0 ∧
      MapsTo (fun t => Z (f t)) D (omegaH lam) ∧
      EqOn b (fun t => highPrefactor lam (Z (f t))) D ∧
      ∀ᶠ ε : ℝ in 𝓝[>] 0, -(ε:ℂ)∈D := by
  have hZ0 := hZ 0 (mem_ball_self hr)
  have hPa : AnalyticAt ℂ (fun u => 1-(spectralProduct lam (Z u))^2) 0 :=
    analyticAt_const.sub (((spectralProduct_analyticAt_ff lam _).comp hZ0).pow 2)
  have hP0 : 1-(spectralProduct lam (Z 0))^2≠0 :=
    sub_ne_zero.mpr (product_sq_ne_one_of_strictU hd hu).symm
  have hfc : ContinuousOn (fun u => highPrefactor lam (Z u)) (upperBall r) := by
    intro u hu
    exact (((highPrefactor_actual_spec hlam).1 _ (hmap hu)).continuousAt.comp
      (hZ u hu.1).continuousAt).continuousWithinAt
  have hpow : ∀u∈upperBall r, (highPrefactor lam (Z u))^4=1-(spectralProduct lam (Z u))^2 :=
    fun u hu => (highPrefactor_actual_spec hlam).2.1 _ (hmap hu)
  obtain ⟨δ,hδ,hδr,g,hg,hg0,hgeq⟩ := exists_upper_fourth_branch_extension hr hPa hP0 hfc hpow
  let D : Set ℂ := {t | AnalyticAt ℂ f t ∧ f t∈upperBall δ}
  have hD : IsOpen D := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    exact ht.1.eventually_analyticAt.and
      (ht.1.continuousAt.tendsto.eventually ((upperBall_isOpen δ).mem_nhds ht.2))
  have hga : AnalyticAt ℂ g 0 := hg 0 (mem_ball_self hδ)
  refine ⟨D,(fun t => g (f t)),hD,hga.fun_comp_of_eq (f := f) hf hf0,?_,?_,?_,?_⟩
  · simpa only [hf0] using hg0
  · intro t ht
    exact hmap ⟨ball_subset_ball hδr ht.2.1,ht.2.2⟩
  · intro t ht
    exact hgeq ht.2
  · have hp : Tendsto (fun ε : ℝ => -(ε:ℂ)) (𝓝[>] 0) (𝓝 0) := by
      have hc : Continuous (fun ε : ℝ => -(ε:ℂ)) := Complex.continuous_ofReal.neg
      simpa only [Complex.ofReal_zero,neg_zero] using
        (hc.continuousAt (x := (0:ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    have hfp : Tendsto (fun ε : ℝ => f (-(ε:ℂ))) (𝓝[>] 0) (𝓝 0) := by
      simpa only [hf0,Function.comp_def] using hf.continuousAt.tendsto.comp hp
    filter_upwards [hin,hfp.eventually (ball_mem_nhds (0:ℂ) hδ),
      hp.eventually hf.eventually_analyticAt] with ε hi hb ha
    exact ⟨ha,hb,hi.2⟩

end
end IsingBulk.Anisotropic.NegativeDominance
