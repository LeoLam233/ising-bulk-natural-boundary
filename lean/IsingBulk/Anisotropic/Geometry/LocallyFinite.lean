import IsingBulk.Anisotropic.Geometry.EdgeIntersections

namespace IsingBulk.Anisotropic
noncomputable section
open scoped Topology

/-- Every compact neighborhood meets only finitely many excluded points locally. -/
def LocallyFiniteSubset (s : Set ℂ) : Prop :=
  ∀ z : ℂ, ∃ U : Set ℂ, IsOpen U ∧ z∈U ∧ (s∩U).Finite

theorem LocallyFiniteSubset.mono {s t : Set ℂ} (ht : LocallyFiniteSubset t) (h : s⊆t) :
    LocallyFiniteSubset s := by
  intro z
  rcases ht z with ⟨U,hU,hz,hfin⟩
  exact ⟨U,hU,hz,hfin.subset (Set.inter_subset_inter_left U h)⟩

theorem LocallyFiniteSubset.union {s t : Set ℂ} (hs : LocallyFiniteSubset s) (ht : LocallyFiniteSubset t) :
    LocallyFiniteSubset (s∪t) := by
  intro z
  rcases hs z with ⟨U,hU,hzU,hfinU⟩
  rcases ht z with ⟨V,hV,hzV,hfinV⟩
  refine ⟨U∩V,hU.inter hV,⟨hzU,hzV⟩,(hfinU.union hfinV).subset ?_⟩
  intro w hw
  rcases hw.1 with h | h
  · exact Or.inl ⟨h,hw.2.1⟩
  · exact Or.inr ⟨h,hw.2.2⟩

theorem analytic_locally_nonzero {𝕜 : Type*} [NontriviallyNormedField 𝕜] [PreconnectedSpace 𝕜]
    {f : 𝕜→𝕜} (hf : ∀ z, AnalyticAt 𝕜 f z) (hne : ∃z,f z≠0) (z : 𝕜) :
    ∀ᶠ w in 𝓝[≠] z, f w≠0 := by
  rcases (hf z).eventually_eq_zero_or_eventually_ne_zero with h | h
  · have ha : AnalyticOnNhd 𝕜 f Set.univ := fun t _ => hf t
    have he := ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ z) h
    rcases hne with ⟨t,ht⟩
    exact False.elim (ht (he (Set.mem_univ t)))
  · exact h

theorem analytic_zeros_locally_finite {f : ℂ→ℂ} (hf : ∀ z,AnalyticAt ℂ f z) (hne : ∃z,f z≠0) :
    LocallyFiniteSubset {z | f z=0} := by
  intro z
  have h := analytic_locally_nonzero hf hne z
  rw [nhdsWithin,Filter.eventually_inf_principal] at h
  have he : ∀ᶠ w in 𝓝 z, f w=0 → w=z := by
    filter_upwards [h] with w hw he
    by_contra hn
    exact hw hn he
  rcases mem_nhds_iff.mp he with ⟨U,hUsub,hU,hz⟩
  refine ⟨U,hU,hz,(Set.finite_singleton z).subset ?_⟩
  intro w hw
  exact Set.mem_singleton_iff.mpr (hUsub hw.2 hw.1)

theorem axis_spectral_locally_finite (lam : ℝ) :
    LocallyFiniteSubset {z : ℂ | z.re=0 ∧ z∈spectralSet lam} := by
  intro z
  have hf : ∀ y:ℝ, AnalyticAt ℝ (fun t => Real.cos t*Real.cos (lam*t)) y := fun _ =>
    Real.analyticAt_cos.mul (Real.analyticAt_cos.comp (analyticAt_const.mul analyticAt_id))
  have h := analytic_locally_nonzero hf ⟨0,by simp⟩ z.im
  rw [nhdsWithin,Filter.eventually_inf_principal] at h
  have he : ∀ᶠ y in 𝓝 z.im, Real.cos y*Real.cos (lam*y)=0 → y=z.im := by
    filter_upwards [h] with y hy he
    by_contra hn
    exact hy hn he
  have hw : ∀ᶠ w in 𝓝 z, w.re=0 ∧ w∈spectralSet lam → w=(z.im:ℂ)*Complex.I := by
    filter_upwards [Complex.continuous_im.continuousAt.preimage_mem_nhds he] with w hw hE
    have hw' : w=(w.im:ℂ)*Complex.I := by apply Complex.ext <;> simp [hE.1]
    have hi := hw ((imaginary_mem_spectralSet_iff lam w.im).mp (hw' ▸ hE.2))
    rw [hw',hi]
  rcases mem_nhds_iff.mp hw with ⟨U,hUsub,hU,hz⟩
  refine ⟨U,hU,hz,(Set.finite_singleton ((z.im:ℂ)*Complex.I)).subset ?_⟩
  intro w hw
  exact Set.mem_singleton_iff.mpr (hUsub hw.2 hw.1)

theorem collinear_spectral_subset_edges_or_axis {lam : ℝ} (hlam : 0<lam) :
    {z | z∈spectralSet lam ∧ spectralDet lam z=0} ⊆
      edgeIntersectionSet lam ∪ {z : ℂ | z.re=0 ∧ z∈spectralSet lam} := by
  have hright {z : ℂ} (hx : 0<z.re) (hz : z∈spectralSet lam) (hd : spectralDet lam z=0) :
      z∈edgeIntersectionSet lam := by
    by_cases hq : Real.sin z.im≠0 ∨ Real.sin (lam*z.im)≠0
    · exact signs_zero_of_collinear_right hlam hx hq hd (geometry_signs_of_mem hlam hz)
    · push Not at hq
      exact signs_zero_of_mem_real_angles hlam hx hq.1 hq.2 hz
  intro z hz
  rcases lt_trichotomy z.re 0 with hx | hx | hx
  · left
    have hn := hright (z := -z) (by simpa using neg_pos.mpr hx)
      ((neg_mem_spectralSet_iff lam z).mpr hz.1) (by
        simpa [spectralDet,spectralS,spectralT,mul_neg,Complex.sinh_neg] using hz.2)
    simpa [edgeIntersectionSet,geometryF1,geometryF2,mul_neg,Real.cosh_neg,Real.sinh_neg,Real.cos_neg] using hn
  · exact Or.inr ⟨hx,hz.1⟩
  · exact Or.inl (hright hx hz.1 hz.2)

/-- Local discreteness of every collinear candidate, including all imaginary-axis points. -/
theorem collinear_spectral_locally_finite {lam : ℝ} (hlam : 0<lam) (hne : lam≠1) :
    LocallyFiniteSubset {z | z∈spectralSet lam ∧ spectralDet lam z=0} := by
  have hE : LocallyFiniteSubset (edgeIntersectionSet lam) := edgeIntersectionSet_locally_finite hlam hne
  exact (hE.union (axis_spectral_locally_finite lam)).mono
    (collinear_spectral_subset_edges_or_axis hlam)

end
end IsingBulk.Anisotropic
