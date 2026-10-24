import IsingBulk.Anisotropic.Geometry.BoundaryDensity

namespace IsingBulk.Anisotropic
noncomputable section
open scoped Topology

def RegularEdgePoint (lam : ℝ) (z : ℂ) : Prop :=
  spectralDet lam z≠0 ∧
  ((∃ e : ℝ, (e=1 ∨ e= -1) ∧ spectralU lam z=e ∧ |spectralV lam z|<1 ∧
      deriv (edgeMapU lam (e:ℂ)) z≠0) ∨
   (∃ e : ℝ, (e=1 ∨ e= -1) ∧ spectralV lam z=e ∧ |spectralU lam z|<1 ∧
      deriv (edgeMapV lam (e:ℂ)) z≠0))

theorem spectralDet_continuous (lam : ℝ) : Continuous (spectralDet lam) := by
  unfold spectralDet spectralS spectralT
  fun_prop

theorem spectralU_continuousAt {lam : ℝ} {z : ℂ} (hd : spectralDet lam z≠0) :
    ContinuousAt (spectralU lam) z := by
  apply ContinuousAt.div _ (spectralDet_continuous lam).continuousAt hd
  unfold spectralNU spectralA spectralT
  fun_prop

theorem spectralV_continuousAt {lam : ℝ} {z : ℂ} (hd : spectralDet lam z≠0) :
    ContinuousAt (spectralV lam) z := by
  apply ContinuousAt.div _ (spectralDet_continuous lam).continuousAt hd
  unfold spectralNV spectralA spectralS
  fun_prop

theorem mem_interior_spectralSet_of_strict_coordinates {lam : ℝ} {z : ℂ}
    (hd : spectralDet lam z≠0) (hu : |spectralU lam z|<1) (hv : |spectralV lam z|<1) :
    z∈interior (spectralSet lam) := by
  apply mem_interior_iff_mem_nhds.mpr
  have hde : ∀ᶠ w in 𝓝 z, spectralDet lam w≠0 :=
    (spectralDet_continuous lam).continuousAt.eventually_ne hd
  have hue : ∀ᶠ w in 𝓝 z, |spectralU lam w|<1 :=
    (spectralU_continuousAt hd).abs.eventually_lt_const hu
  have hve : ∀ᶠ w in 𝓝 z, |spectralV lam w|<1 :=
    (spectralV_continuousAt hd).abs.eventually_lt_const hv
  filter_upwards [hde,hue,hve] with w hwd hwu hwv
  exact (mem_spectralSet_iff_coordinates hwd).mpr ⟨hwu.le,hwv.le⟩

theorem product_sq_eq_one_of_coordinate_corner {lam : ℝ} {z : ℂ}
    (hd : spectralDet lam z≠0) (hu : |spectralU lam z|=1) (hv : |spectralV lam z|=1) :
    spectralProduct lam z^2=1 := by
  have hu' : (spectralU lam z)^2=1 := by nlinarith [sq_abs (spectralU lam z)]
  have hv' : (spectralV lam z)^2=1 := by nlinarith [sq_abs (spectralV lam z)]
  have hu2 : (spectralU lam z:ℂ)^2=1 := by exact_mod_cast hu'
  have hv2 : (spectralV lam z:ℂ)^2=1 := by exact_mod_cast hv'
  have hc := spectral_corner_identity lam z (spectralU lam z) (spectralV lam z) hu2 hv2
  have hr : spectralA lam z=(spectralU lam z:ℂ)*spectralS z+(spectralV lam z:ℂ)*spectralT lam z := by
    simpa only [mul_comm] using spectral_reconstruction hd
  rw [←hr,sub_self] at hc
  have hp : spectralProduct lam z=(spectralU lam z:ℂ)*(spectralV lam z:ℂ) :=
    sub_eq_zero.mp (sq_eq_zero_iff.mp hc.symm)
  rw [hp,mul_pow,hu2,hv2,one_mul]

theorem regularEdgePoint_of_spectral_boundary {lam : ℝ} {z : ℂ}
    (hz : z∈spectralSet lam) (hint : z∉interior (spectralSet lam))
    (he : z∉edgeExceptionalSet lam) : RegularEdgePoint lam z := by
  have he' : ¬(z∈spectralSet lam ∧ spectralDet lam z=0) ∧ spectralS z≠0 ∧ spectralT lam z≠0 ∧
      spectralProduct lam z^2≠1 ∧ edgeNumeratorU lam 1 z≠0 ∧ edgeNumeratorU lam (-1) z≠0 ∧
      edgeNumeratorV lam 1 z≠0 ∧ edgeNumeratorV lam (-1) z≠0 := by
    simpa only [edgeExceptionalSet,Set.mem_union,Set.mem_ofPred_eq,or_assoc,not_or] using he
  have hd : spectralDet lam z≠0 := fun h => he'.1 ⟨hz,h⟩
  rcases he' with ⟨_,hs,ht,hp,hU1,hUn,hV1,hVn⟩
  have hu : |spectralU lam z|≤1 := ((mem_spectralSet_iff_coordinates hd).mp hz).1
  have hv : |spectralV lam z|≤1 := ((mem_spectralSet_iff_coordinates hd).mp hz).2
  refine ⟨hd,?_⟩
  by_cases hu' : |spectralU lam z|<1
  · have hv' : |spectralV lam z|=1 := le_antisymm hv (le_of_not_gt (fun h => hint
      (mem_interior_spectralSet_of_strict_coordinates hd hu' h)))
    have hcases : spectralV lam z=1 ∨ spectralV lam z= -1 := (abs_eq (by norm_num : (0:ℝ)≤1)).mp hv'
    refine Or.inr ⟨spectralV lam z,hcases,rfl,hu',?_⟩
    rw [(edgeMapV_hasDerivAt lam _ z hs).deriv]
    apply div_ne_zero _ (pow_ne_zero _ hs)
    rcases hcases with h | h
    · simpa only [h,Complex.ofReal_one] using hV1
    · simpa only [h,Complex.ofReal_neg,Complex.ofReal_one] using hVn
  · have hue : |spectralU lam z|=1 := le_antisymm hu (le_of_not_gt hu')
    have hvl : |spectralV lam z|<1 := lt_of_le_of_ne hv (fun h => hp
      (product_sq_eq_one_of_coordinate_corner hd hue h))
    have hcases : spectralU lam z=1 ∨ spectralU lam z= -1 := (abs_eq (by norm_num : (0:ℝ)≤1)).mp hue
    refine Or.inl ⟨spectralU lam z,hcases,rfl,hvl,?_⟩
    rw [(edgeMapU_hasDerivAt lam _ z ht).deriv]
    apply div_ne_zero _ (pow_ne_zero _ ht)
    rcases hcases with h | h
    · simpa only [h,Complex.ofReal_one] using hU1
    · simpa only [h,Complex.ofReal_neg,Complex.ofReal_one] using hUn


theorem frontier_not_mem_interior_of_subset_compl {U E : Set ℂ} (hU : U⊆Eᶜ)
    {z : ℂ} (hz : z∈frontier U) : z∉interior E := by
  intro hi
  rcases mem_closure_iff.mp (frontier_subset_closure hz) _ isOpen_interior hi with ⟨w,hwi,hwU⟩
  exact hU hwU (interior_subset hwi)

theorem regularEdgePoint_on_omegaH_frontier {lam : ℝ} (hlam : 0<lam) {z : ℂ}
    (hz : z∈frontier (omegaH lam)) (he : z∉edgeExceptionalSet lam) : RegularEdgePoint lam z :=
  regularEdgePoint_of_spectral_boundary (frontier_omegaH_subset_spectralSet hlam hz)
    (frontier_not_mem_interior_of_subset_compl (omegaH_subset_spectral_complement hlam) hz) he

theorem regularEdgePoint_on_omegaL_frontier {lam : ℝ} (hlam : 0<lam) {z : ℂ}
    (hz : z∈frontier (omegaL lam)) (he : z∉edgeExceptionalSet lam) : RegularEdgePoint lam z :=
  regularEdgePoint_of_spectral_boundary (frontier_omegaL_subset_spectralSet hlam hz)
    (frontier_not_mem_interior_of_subset_compl (omegaL_subset_spectral_complement hlam) hz) he

/-- Actual regular edge points are dense on the entire HT lens boundary, not just away from its tips. -/
theorem frontier_omegaH_subset_closure_regular {lam : ℝ} (hlam : 0<lam) (hne : lam≠1) :
    frontier (omegaH lam) ⊆ closure {z | z∈frontier (omegaH lam) ∧ RegularEdgePoint lam z} := by
  apply Set.Subset.trans (frontier_omegaH_subset_closure_diff_locallyFinite hlam
    (edgeExceptionalSet_locally_finite hlam hne))
  apply closure_mono
  intro z hz
  exact ⟨hz.1,regularEdgePoint_on_omegaH_frontier hlam hz.1 hz.2⟩

/-- Actual regular edge points are dense on the entire LT frontier. -/
theorem frontier_omegaL_subset_closure_regular {lam : ℝ} (hlam : 0<lam) (hne : lam≠1) :
    frontier (omegaL lam) ⊆ closure {z | z∈frontier (omegaL lam) ∧ RegularEdgePoint lam z} := by
  apply Set.Subset.trans (frontier_omegaL_subset_closure_diff_locallyFinite hlam
    (edgeExceptionalSet_locally_finite hlam hne))
  apply closure_mono
  intro z hz
  exact ⟨hz.1,regularEdgePoint_on_omegaL_frontier hlam hz.1 hz.2⟩

end
end IsingBulk.Anisotropic
