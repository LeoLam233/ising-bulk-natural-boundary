import IsingBulk.AnisoF002.Geometry.HighProfiles
import IsingBulk.AnisoF002.Geometry.LowSimpleConnectivity

/-!
# The complete high-temperature lens is the physical complement component

F002 theorem 2.2 (thm:components), HT part.  The actual finite-width lens is
star shaped, including contraction of its closed boundary and both tips.
Its entire frontier is the exact profile curve.  The F002 endpoint boundary
criterion and the actual zero-coupling spectral seed determine the whole
component; no historical component/sign-characterization endpoint is used.
-/

namespace IsingBulk.AnisoF002.Geometry
noncomputable section
open IsingBulk.Anisotropic Set

theorem profileP_sq_abs (lam x : ℝ) :
    profilePF002 lam |x| ^ 2 = profilePF002 lam x ^ 2 := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_nonpos hx, profileP_neg, neg_sq]

theorem profileQ_neg (lam x : ℝ) :
    profileQF002 lam (-x) = -profileQF002 lam x := by
  simp only [profileQF002, mul_neg, Real.cosh_neg, Real.tanh_neg]

theorem profileQ_sq_abs (lam x : ℝ) :
    profileQF002 lam |x| ^ 2 = profileQF002 lam x ^ 2 := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_nonpos hx, profileQ_neg, neg_sq]

theorem isOpen_omegaHF002 {lam : ℝ} (hlam : 0 < lam) :
    IsOpen (omegaHF002 lam) := by
  exact (isOpen_lt Complex.continuous_im.abs continuous_const).inter
    (isOpen_lt Complex.continuous_re.abs
      ((highProfile_continuous hlam).comp Complex.continuous_im))

theorem zero_mem_omegaHF002 {lam : ℝ} (hlam : 0 < lam) :
    (0 : ℂ) ∈ omegaHF002 lam := by
  constructor
  · simpa using (highStripWidth_bounds hlam).1
  · simpa [highProfile_zero hlam] using criticalPointF002_pos hlam

theorem zero_not_mem_spectralSetF002 (lam : ℝ) :
    (0 : ℂ) ∉ spectralSetF002 lam := by
  rintro ⟨u, _, v, _, h⟩
  delta spectralA spectralS spectralT at h
  norm_num at h

/-- Every strict radial contraction of the closed lens enters the open lens,
including contractions of both finite imaginary-axis tips. -/
theorem closed_lens_contraction {lam a : ℝ} {z : ℂ} (hlam : 0 < lam)
    (hy : |z.im| ≤ highStripWidthF002 lam)
    (hx : |z.re| ≤ highProfileF002 lam z.im)
    (ha : 0 ≤ a) (ha1 : a < 1) : a • z ∈ omegaHF002 lam := by
  have hY := (highStripWidth_bounds hlam).1
  have hay : |a * z.im| < highStripWidthF002 lam := by
    rw [abs_mul, abs_of_nonneg ha]
    calc
      a * |z.im| ≤ a * highStripWidthF002 lam := mul_le_mul_of_nonneg_left hy ha
      _ < highStripWidthF002 lam := by nlinarith
  have hH := highProfile_contraction hlam ha ha1.le hy
  have hax : |a * z.re| < highProfileF002 lam (a * z.im) := by
    rw [abs_mul, abs_of_nonneg ha]
    by_cases hx0 : |z.re| = 0
    · rw [hx0, mul_zero]
      exact highProfile_pos hlam hay
    · have hp : 0 < |z.re| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hx0)
      have hstrict : a * |z.re| < |z.re| := by nlinarith
      exact lt_of_lt_of_le hstrict (hx.trans hH)
  change |(a • z).im| < highStripWidthF002 lam ∧
    |(a • z).re| < highProfileF002 lam (a • z).im
  simpa only [Complex.smul_im, Complex.smul_re, smul_eq_mul] using And.intro hay hax

theorem omegaHF002_starConvex {lam : ℝ} (hlam : 0 < lam) :
    StarConvex ℝ (0 : ℂ) (omegaHF002 lam) := by
  apply starConvex_zero_iff.mpr
  intro z hz a ha ha1
  rcases lt_or_eq_of_le ha1 with hlt | heq
  · exact closed_lens_contraction hlam hz.1.le hz.2.le ha hlt
  · subst a
    simpa only [one_smul] using hz

theorem omegaHF002_isSimplyConnected {lam : ℝ} (hlam : 0 < lam) :
    IsSimplyConnected (omegaHF002 lam) := by
  change SimplyConnectedSpace _
  exact @SimplyConnectedSpace.ofContractible _ _
    ((omegaHF002_starConvex hlam).contractibleSpace ⟨0, zero_mem_omegaHF002 hlam⟩)

theorem omegaHF002_isPreconnected {lam : ℝ} (hlam : 0 < lam) :
    IsPreconnected (omegaHF002 lam) :=
  (omegaHF002_isSimplyConnected hlam).isPathConnected.isConnected.isPreconnected

theorem closure_omegaHF002 {lam : ℝ} (hlam : 0 < lam) :
    closure (omegaHF002 lam) =
      {z : ℂ | |z.im| ≤ highStripWidthF002 lam ∧ |z.re| ≤ highProfileF002 lam z.im} := by
  apply Set.Subset.antisymm
  · apply closure_minimal
    · exact fun _ hz => ⟨hz.1.le, hz.2.le⟩
    · exact (isClosed_le Complex.continuous_im.abs continuous_const).inter
        (isClosed_le Complex.continuous_re.abs
          ((highProfile_continuous hlam).comp Complex.continuous_im))
  · intro z hz
    have h1 : (1 : ℝ) ∈ closure (Set.Ioo (0 : ℝ) 1) := by
      rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
      simp
    have hf : Continuous (fun a : ℝ => a • z) := continuous_id.smul continuous_const
    have hc := mem_closure_image hf.continuousAt h1
    have hsub : (fun a : ℝ => a • z) '' Set.Ioo 0 1 ⊆ omegaHF002 lam := by
      rintro w ⟨a, ha, rfl⟩
      exact closed_lens_contraction hlam hz.1 hz.2 ha.1.le ha.2
    have hh := closure_mono hsub hc
    simpa only [one_smul] using hh

theorem frontier_omegaHF002 {lam : ℝ} (hlam : 0 < lam) :
    frontier (omegaHF002 lam) =
      {z : ℂ | |z.im| ≤ highStripWidthF002 lam ∧ |z.re| = highProfileF002 lam z.im} := by
  ext z
  rw [frontier, (isOpen_omegaHF002 hlam).interior_eq, closure_omegaHF002 hlam]
  constructor
  · rintro ⟨hz, hn⟩
    refine ⟨hz.1, ?_⟩
    by_cases hy : |z.im| < highStripWidthF002 lam
    · exact le_antisymm hz.2 (le_of_not_gt (fun hx => hn ⟨hy, hx⟩))
    · have htip : |z.im| = highStripWidthF002 lam := le_antisymm hz.1 (le_of_not_gt hy)
      have hH := highProfile_tip_zero hlam htip
      exact le_antisymm hz.2 (by rw [hH]; exact abs_nonneg _)
  · rintro ⟨hy, hx⟩
    refine ⟨⟨hy, hx.le⟩, ?_⟩
    intro hz
    exact (not_lt_of_ge hx.ge) hz.2

theorem highProfile_graph_endpoint {lam : ℝ} (hlam : 0 < lam) {z : ℂ}
    (hz : |z.re| = highProfileF002 lam z.im) : z ∈ endpointLocusF002 lam := by
  let a := profilePInvF002 lam (Real.cos z.im)
  let b := profileQInvF002 lam (Real.cos (lam * z.im))
  change |z.re| = min a b at hz
  by_cases hab : a ≤ b
  · have hx : |z.re| = a := hz.trans (min_eq_left hab)
    have hP : profilePF002 lam |z.re| = Real.cos z.im := by
      rw [hx]
      exact profileP_rightInverse hlam _
    have hP2 : profilePF002 lam z.re ^ 2 = Real.cos z.im ^ 2 := by
      rw [← profileP_sq_abs lam z.re, hP]
    have hF : geometryF1 lam z.re z.im = 0 := by
      rw [geometryF1_profile_factor, hP2, sub_self, mul_zero]
    change geometryF1 lam z.re z.im * geometryF2 lam z.re z.im = 0
    rw [hF, zero_mul]
  · have hx : |z.re| = b := hz.trans (min_eq_right (le_of_not_ge hab))
    have hQ : profileQF002 lam |z.re| = Real.cos (lam * z.im) := by
      rw [hx]
      exact profileQ_rightInverse hlam _
    have hQ2 : profileQF002 lam z.re ^ 2 = Real.cos (lam * z.im) ^ 2 := by
      rw [← profileQ_sq_abs lam z.re, hQ]
    have hF : geometryF2 lam z.re z.im = 0 := by
      rw [geometryF2_profile_factor, hQ2, sub_self, mul_zero]
    change geometryF1 lam z.re z.im * geometryF2 lam z.re z.im = 0
    rw [hF, mul_zero]

theorem frontier_omegaHF002_subset_endpoint {lam : ℝ} (hlam : 0 < lam) :
    frontier (omegaHF002 lam) ⊆ endpointLocusF002 lam := by
  rw [frontier_omegaHF002 hlam]
  exact fun _ hz => highProfile_graph_endpoint hlam hz.2

theorem omegaHF002_endpoint_signs {lam : ℝ} (hlam : 0 < lam) {z : ℂ}
    (hz : z ∈ omegaHF002 lam) :
    0 < geometryF1 lam z.re z.im ∧ 0 < geometryF2 lam z.re z.im := by
  obtain ⟨hc1, hc2⟩ := high_strip_cosines_pos hlam hz.1
  have hp : |z.re| < profilePInvF002 lam (Real.cos z.im) :=
    lt_of_lt_of_le hz.2 (min_le_left _ _)
  have hq : |z.re| < profileQInvF002 lam (Real.cos (lam * z.im)) :=
    lt_of_lt_of_le hz.2 (min_le_right _ _)
  have hP := profileP_strictMono hlam hp
  have hQ := profileQ_strictMono hlam hq
  rw [profileP_rightInverse hlam _] at hP
  rw [profileQ_rightInverse hlam _] at hQ
  have hP0 : 0 ≤ profilePF002 lam |z.re| := by
    have hh := (profileP_strictMono hlam).monotone (abs_nonneg z.re)
    simpa only [profileP_zero] using hh
  have hQ0 : 0 ≤ profileQF002 lam |z.re| := by
    have hh := (profileQ_strictMono hlam).monotone (abs_nonneg z.re)
    simpa only [profileQ_zero] using hh
  have hP2 : profilePF002 lam z.re ^ 2 < Real.cos z.im ^ 2 := by
    have hh := (sq_lt_sq₀ hP0 hc1.le).mpr hP
    simpa only [profileP_sq_abs] using hh
  have hQ2 : profileQF002 lam z.re ^ 2 < Real.cos (lam * z.im) ^ 2 := by
    have hh := (sq_lt_sq₀ hQ0 hc2.le).mpr hQ
    simpa only [profileQ_sq_abs] using hh
  constructor
  · rw [geometryF1_profile_factor]
    exact mul_pos (sq_pos_of_pos (Real.cosh_pos _)) (sub_pos.mpr hP2)
  · rw [geometryF2_profile_factor]
    exact mul_pos (sq_pos_of_pos (Real.cosh_pos _)) (sub_pos.mpr hQ2)

theorem omegaHF002_subset_complement {lam : ℝ} (hlam : 0 < lam) :
    omegaHF002 lam ⊆ (spectralSetF002 lam)ᶜ := by
  apply preconnected_endpoint_free_subset_complement hlam (omegaHF002_isPreconnected hlam)
  · intro z hz hE
    obtain ⟨hF1, hF2⟩ := omegaHF002_endpoint_signs hlam hz
    exact (ne_of_gt (mul_pos hF1 hF2)) hE
  · exact ⟨0, zero_mem_omegaHF002 hlam, zero_not_mem_spectralSetF002 lam⟩

theorem omegaHF002_eq_component {lam : ℝ} (hlam : 0 < lam) {z₀ : ℂ}
    (hz₀ : z₀ ∈ omegaHF002 lam) :
    connectedComponentIn (spectralSetF002 lam)ᶜ z₀ = omegaHF002 lam := by
  have hsub := omegaHF002_subset_complement hlam
  have hC : IsPreconnected (connectedComponentIn (spectralSetF002 lam)ᶜ z₀) :=
    isPreconnected_connectedComponentIn
  apply Set.Subset.antisymm
  · apply hC.subset_of_closure_inter_subset (isOpen_omegaHF002 hlam)
      ⟨z₀, mem_connectedComponentIn (hsub hz₀), hz₀⟩
    intro z hz
    by_contra hnot
    have hfront : z ∈ frontier (omegaHF002 lam) := by
      refine ⟨hz.1, ?_⟩
      rwa [(isOpen_omegaHF002 hlam).interior_eq]
    have hspec := (endpoint_boundary_criterion hlam).1
      (frontier_omegaHF002_subset_endpoint hlam hfront)
    exact (connectedComponentIn_subset _ _ hz.2) hspec
  · exact (omegaHF002_isPreconnected hlam).subset_connectedComponentIn hz₀ hsub

theorem real_mem_omegaHF002 {lam x : ℝ} (hlam : 0 < lam)
    (hx : 0 < x) (hxc : x < criticalPointF002 lam) : (x : ℂ) ∈ omegaHF002 lam := by
  constructor
  · simpa using (highStripWidth_bounds hlam).1
  · simpa [highProfile_zero hlam, abs_of_pos hx] using hxc

/-- The whole physical HT component, for every original positive real seed. -/
theorem omegaHF002_eq_physical_component {lam x : ℝ} (hlam : 0 < lam)
    (hx : 0 < x) (hxc : x < criticalPointF002 lam) :
    connectedComponentIn (spectralSetF002 lam)ᶜ (x : ℂ) = omegaHF002 lam :=
  omegaHF002_eq_component hlam (real_mem_omegaHF002 hlam hx hxc)

end
end IsingBulk.AnisoF002.Geometry

