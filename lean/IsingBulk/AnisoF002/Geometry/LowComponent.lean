import IsingBulk.AnisoF002.Geometry.ProfileBounds
import IsingBulk.AnisoF002.Geometry.CanonicalRootPhysical

/-!
# The complete low-temperature epigraph is the physical complement component

F002 `thm:components`, low-temperature part, proved by the paper's endpoint
boundary criterion.  This proof does not invoke the historical complete
spectral sign characterization.  Both endpoint factors are negative in the
actual epigraph; its complete boundary graph lies in the endpoint locus.
Connectedness and the new boundary criterion then determine the component.
-/

namespace IsingBulk.AnisoF002.Geometry
noncomputable section
open IsingBulk.Anisotropic Set

theorem geometryF1_profile_factor (lam x y : ℝ) :
    geometryF1 lam x y =
      Real.cosh (lam * x) ^ 2 * (Real.cos y ^ 2 - profilePF002 lam x ^ 2) := by
  delta geometryF1 profilePF002
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp [ne_of_gt (Real.cosh_pos (lam * x))]

theorem geometryF2_profile_factor (lam x y : ℝ) :
    geometryF2 lam x y =
      Real.cosh x ^ 2 * (Real.cos (lam * y) ^ 2 - profileQF002 lam x ^ 2) := by
  delta geometryF2 profileQF002
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp [ne_of_gt (Real.cosh_pos x)]

theorem omegaLF002_endpoint_signs {lam : ℝ} (hlam : 0 < lam) {z : ℂ}
    (hz : z ∈ omegaLF002 lam) :
    geometryF1 lam z.re z.im < 0 ∧ geometryF2 lam z.re z.im < 0 := by
  have hp : profilePInvF002 lam |Real.cos z.im| < z.re :=
    lt_of_le_of_lt (le_max_left _ _) hz
  have hq : profileQInvF002 lam |Real.cos (lam * z.im)| < z.re :=
    lt_of_le_of_lt (le_max_right _ _) hz
  have hP := profileP_strictMono hlam hp
  have hQ := profileQ_strictMono hlam hq
  rw [profileP_rightInverse hlam _] at hP
  rw [profileQ_rightInverse hlam _] at hQ
  have hP2 : Real.cos z.im ^ 2 < profilePF002 lam z.re ^ 2 := by
    have hh := (sq_lt_sq₀ (abs_nonneg (Real.cos z.im))
      (le_trans (abs_nonneg _) hP.le)).mpr hP
    simpa only [sq_abs] using hh
  have hQ2 : Real.cos (lam * z.im) ^ 2 < profileQF002 lam z.re ^ 2 := by
    have hh := (sq_lt_sq₀ (abs_nonneg (Real.cos (lam * z.im)))
      (le_trans (abs_nonneg _) hQ.le)).mpr hQ
    simpa only [sq_abs] using hh
  constructor
  · rw [geometryF1_profile_factor]
    exact mul_neg_of_pos_of_neg (sq_pos_of_pos (Real.cosh_pos _)) (sub_neg.mpr hP2)
  · rw [geometryF2_profile_factor]
    exact mul_neg_of_pos_of_neg (sq_pos_of_pos (Real.cosh_pos _)) (sub_neg.mpr hQ2)

theorem lowProfile_graph_endpoint {lam : ℝ} (hlam : 0 < lam) {z : ℂ}
    (hz : lowProfileF002 lam z.im = z.re) : z ∈ endpointLocusF002 lam := by
  let a := profilePInvF002 lam |Real.cos z.im|
  let b := profileQInvF002 lam |Real.cos (lam * z.im)|
  change max a b = z.re at hz
  by_cases hab : a ≤ b
  · have hx : z.re = b := hz.symm.trans (max_eq_right hab)
    have hQ : profileQF002 lam z.re = |Real.cos (lam * z.im)| := by
      rw [hx]
      exact profileQ_rightInverse hlam _
    have hF : geometryF2 lam z.re z.im = 0 := by
      rw [geometryF2_profile_factor, hQ, sq_abs, sub_self, mul_zero]
    change geometryF1 lam z.re z.im * geometryF2 lam z.re z.im = 0
    rw [hF, mul_zero]
  · have hx : z.re = a := hz.symm.trans (max_eq_left (le_of_not_ge hab))
    have hP : profilePF002 lam z.re = |Real.cos z.im| := by
      rw [hx]
      exact profileP_rightInverse hlam _
    have hF : geometryF1 lam z.re z.im = 0 := by
      rw [geometryF1_profile_factor, hP, sq_abs, sub_self, mul_zero]
    change geometryF1 lam z.re z.im * geometryF2 lam z.re z.im = 0
    rw [hF, zero_mul]

theorem frontier_omegaLF002 {lam : ℝ} (hlam : 0 < lam) :
    frontier (omegaLF002 lam) = {z : ℂ | lowProfileF002 lam z.im = z.re} := by
  apply Set.Subset.antisymm
  · exact frontier_lt_subset_eq
      ((lowProfile_continuous hlam).comp Complex.continuous_im) Complex.continuous_re
  · intro z hz
    change lowProfileF002 lam z.im = z.re at hz
    refine ⟨?_, ?_⟩
    · apply Metric.mem_closure_iff.mpr
      intro r hr
      refine ⟨z + ((r / 2 : ℝ) : ℂ), ?_, ?_⟩
      · change lowProfileF002 lam (z + ((r / 2 : ℝ) : ℂ)).im <
          (z + ((r / 2 : ℝ) : ℂ)).re
        simp only [Complex.add_im, Complex.add_re, Complex.ofReal_im, Complex.ofReal_re, add_zero]
        linarith
      · have hd : dist z (z + ((r / 2 : ℝ) : ℂ)) = r / 2 := by
          rw [dist_eq_norm]
          calc
            ‖z - (z + ((r / 2 : ℝ) : ℂ))‖ = ‖-((r / 2 : ℝ) : ℂ)‖ := by congr 1; ring
            _ = r / 2 := by
              rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
        rw [hd]
        linarith
    · rw [(isOpen_omegaLF002 hlam).interior_eq]
      change ¬lowProfileF002 lam z.im < z.re
      exact not_lt_of_ge hz.ge

theorem frontier_omegaLF002_subset_endpoint {lam : ℝ} (hlam : 0 < lam) :
    frontier (omegaLF002 lam) ⊆ endpointLocusF002 lam := by
  rw [frontier_omegaLF002 hlam]
  exact fun _ hz => lowProfile_graph_endpoint hlam hz

theorem omegaLF002_isPreconnected {lam : ℝ} (hlam : 0 < lam) :
    IsPreconnected (omegaLF002 lam) := by
  let f : ℝ × ℝ → ℂ := fun p => ((p.1 + lowProfileF002 lam p.2 : ℝ) : ℂ) +
    (p.2 : ℂ) * Complex.I
  have hL := lowProfile_continuous hlam
  have hf : Continuous f := by
    unfold f
    fun_prop
  have heq : f '' (Set.Ioi (0 : ℝ) ×ˢ Set.univ) = omegaLF002 lam := by
    ext z
    constructor
    · rintro ⟨p, hp, rfl⟩
      change lowProfileF002 lam (f p).im < (f p).re
      simpa [f] using hp.1
    · intro hz
      change lowProfileF002 lam z.im < z.re at hz
      refine ⟨(z.re - lowProfileF002 lam z.im, z.im), ⟨?_, Set.mem_univ _⟩, ?_⟩
      · change 0 < z.re - lowProfileF002 lam z.im
        exact sub_pos.mpr hz
      · apply Complex.ext <;> simp [f]
  rw [← heq]
  exact (isPreconnected_Ioi.prod isPreconnected_univ).image f hf.continuousOn

/-- The endpoint boundary criterion gives the paper's clopen argument on
any connected endpoint-free set containing one spectral-complement seed. -/
theorem preconnected_endpoint_free_subset_complement {lam : ℝ} (hlam : 0 < lam)
    {U : Set ℂ} (hU : IsPreconnected U) (hUE : U ⊆ (endpointLocusF002 lam)ᶜ)
    (hseed : (U ∩ (spectralSetF002 lam)ᶜ).Nonempty) : U ⊆ (spectralSetF002 lam)ᶜ := by
  have hOpen := (isClosed_spectralSetF002 lam).isOpen_compl
  apply hU.subset_of_closure_inter_subset hOpen hseed
  intro z hz
  by_contra hnot
  have hfront : z ∈ frontier ((spectralSetF002 lam)ᶜ) := by
    refine ⟨hz.1, ?_⟩
    rwa [hOpen.interior_eq]
  rw [frontier_compl] at hfront
  exact hUE hz.2 (frontier_subset_endpointLocusF002 hlam hfront)

theorem real_above_critical_not_mem_spectralSetF002 {lam x : ℝ} (hlam : 0 < lam)
    (hx : criticalPointF002 lam < x) : (x : ℂ) ∉ spectralSetF002 lam := by
  have hxpos := lt_trans (criticalPointF002_pos hlam) hx
  apply positive_real_not_mem_spectralSetF002 hlam hxpos
  intro hp
  exact (ne_of_gt hx) (criticalPointF002_unique hlam hxpos hp)

theorem omegaLF002_subset_complement {lam : ℝ} (hlam : 0 < lam) :
    omegaLF002 lam ⊆ (spectralSetF002 lam)ᶜ := by
  apply preconnected_endpoint_free_subset_complement hlam (omegaLF002_isPreconnected hlam)
  · intro z hz hE
    obtain ⟨hF1, hF2⟩ := omegaLF002_endpoint_signs hlam hz
    exact (ne_of_gt (mul_pos_of_neg_of_neg hF1 hF2)) hE
  · refine ⟨((criticalPointF002 lam + 1 : ℝ) : ℂ), ?_, ?_⟩
    · exact (real_mem_omegaLF002_iff hlam).mpr (by linarith)
    · exact real_above_critical_not_mem_spectralSetF002 hlam (by linarith)

/-- The full physical LT complement component, with every finite height in
the epigraph included.  No generic-ratio or regular-boundary restriction. -/
theorem omegaLF002_eq_physical_component {lam x : ℝ} (hlam : 0 < lam)
    (hx : criticalPointF002 lam < x) :
    connectedComponentIn (spectralSetF002 lam)ᶜ (x : ℂ) = omegaLF002 lam := by
  have hxin : (x : ℂ) ∈ omegaLF002 lam := (real_mem_omegaLF002_iff hlam).mpr hx
  have hsub := omegaLF002_subset_complement hlam
  have hC : IsPreconnected (connectedComponentIn (spectralSetF002 lam)ᶜ (x : ℂ)) :=
    isPreconnected_connectedComponentIn
  apply Set.Subset.antisymm
  · apply hC.subset_of_closure_inter_subset (isOpen_omegaLF002 hlam)
      ⟨(x : ℂ), mem_connectedComponentIn (hsub hxin), hxin⟩
    intro z hz
    by_contra hnot
    have hfront : z ∈ frontier (omegaLF002 lam) := by
      refine ⟨hz.1, ?_⟩
      rwa [(isOpen_omegaLF002 hlam).interior_eq]
    have hspec := (endpoint_boundary_criterion hlam).1
      (frontier_omegaLF002_subset_endpoint hlam hfront)
    exact (connectedComponentIn_subset _ _ hz.2) hspec
  · exact (omegaLF002_isPreconnected hlam).subset_connectedComponentIn hxin hsub

end
end IsingBulk.AnisoF002.Geometry
