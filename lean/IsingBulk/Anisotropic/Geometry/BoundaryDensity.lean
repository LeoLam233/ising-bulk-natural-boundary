import IsingBulk.Anisotropic.Geometry.ExceptionalEdges
import IsingBulk.Anisotropic.Geometry.LensBoundary

namespace IsingBulk.Anisotropic
noncomputable section
open scoped Topology

theorem LocallyFiniteSubset.eventually_curve_avoids {E : Set ℂ} (hE : LocallyFiniteSubset E)
    {g : ℝ→ℂ} (hg : Continuous g) (hinj : Function.Injective g) (a : ℝ) :
    ∀ᶠ t in 𝓝[≠] a, g t∉E := by
  rcases hE (g a) with ⟨U,hU,ha,hfin⟩
  have hf : (g ⁻¹' (E∩U)).Finite := hfin.preimage hinj.injOn
  have hav : ∀ᶠ t in 𝓝[≠] a, t∉g ⁻¹' (E∩U) :=
    (nhdsNE_le_cofinite a) (by
      change (g ⁻¹' (E∩U))ᶜ ∈ Filter.cofinite
      exact hf.compl_mem_cofinite)
  have hu : ∀ᶠ t in 𝓝[≠] a, g t∈U :=
    nhdsWithin_le_nhds (hg.continuousAt.preimage_mem_nhds (hU.mem_nhds ha))
  filter_upwards [hav,hu] with t ht htu
  exact fun hte => ht ⟨hte,htu⟩

theorem curve_closure_subset_closure_diff {E s : Set ℂ} (hE : LocallyFiniteSubset E)
    {g : ℝ→ℂ} (hg : Continuous g) (hinj : Function.Injective g)
    {D : Set ℝ} (hD : IsOpen D) (hmap : Set.MapsTo g D s) :
    g '' closure D ⊆ closure (s\E) := by
  have hsub : D ⊆ g ⁻¹' closure (s\E) := by
    intro a ha
    apply mem_closure_iff.mpr
    intro V hV haV
    have hav := hE.eventually_curve_avoids hg hinj a
    have hd : ∀ᶠ t in 𝓝[≠] a, t∈D := nhdsWithin_le_nhds (hD.mem_nhds ha)
    have hv : ∀ᶠ t in 𝓝[≠] a, g t∈V :=
      nhdsWithin_le_nhds (hg.continuousAt.preimage_mem_nhds (hV.mem_nhds haV))
    rcases (hav.and (hd.and hv)).exists with ⟨t,hte,htd,htv⟩
    exact ⟨g t,htv,hmap htd,hte⟩
  rintro z ⟨a,ha,rfl⟩
  exact closure_minimal hsub (isClosed_closure.preimage hg) ha


theorem frontier_omegaL_subset_closure_diff_locallyFinite {lam : ℝ} (hlam : 0<lam)
    {E : Set ℂ} (hE : LocallyFiniteSubset E) :
    frontier (omegaL lam) ⊆ closure (frontier (omegaL lam)\E) := by
  let g : ℝ→ℂ := fun y => (sliceL lam y:ℂ)+(y:ℂ)*Complex.I
  have hg : Continuous g := (Complex.continuous_ofReal.comp (sliceL_continuous hlam)).add
    (Complex.continuous_ofReal.mul_const Complex.I)
  have hi : Function.Injective g := by
    intro x y h
    simpa [g] using congrArg Complex.im h
  have hm : Set.MapsTo g Set.univ (frontier (omegaL lam)) := by
    intro y _
    apply (mem_frontier_omegaL_iff hlam _).mpr
    simp [g]
  intro z hz
  apply curve_closure_subset_closure_diff hE hg hi isOpen_univ hm
  refine ⟨z.im,by simp,?_⟩
  apply Complex.ext
  · simpa [g] using ((mem_frontier_omegaL_iff hlam z).mp hz).symm
  · simp [g]

theorem frontier_omegaH_subset_closure_diff_locallyFinite {lam : ℝ} (hlam : 0<lam)
    {E : Set ℂ} (hE : LocallyFiniteSubset E) :
    frontier (omegaH lam) ⊆ closure (frontier (omegaH lam)\E) := by
  have he (e : ℝ) (he : |e|=1) (y : ℝ) (hy : |y|≤sliceY lam) :
      highBoundaryPoint lam e y∈closure (frontier (omegaH lam)\E) := by
    have hi : Function.Injective (highBoundaryPoint lam e) := by
      intro a b h
      simpa [highBoundaryPoint] using congrArg Complex.im h
    have hm : Set.MapsTo (highBoundaryPoint lam e) (Set.Ioo (-sliceY lam) (sliceY lam))
        (frontier (omegaH lam)) := fun _ ht => highBoundaryPoint_mem_frontier_open hlam he (abs_lt.mpr ht)
    apply curve_closure_subset_closure_diff hE (highBoundaryPoint_continuous hlam e) hi isOpen_Ioo hm
    refine ⟨y,?_,rfl⟩
    rw [closure_Ioo (by linarith [sliceY_pos hlam] : -sliceY lam≠sliceY lam)]
    exact abs_le.mp hy
  intro z hz
  rcases (mem_frontier_omegaH_iff hlam z).mp hz with ⟨hy,hx⟩
  by_cases hr : 0≤z.re
  · have hz' : z=highBoundaryPoint lam 1 z.im := by
      apply Complex.ext
      · simpa [highBoundaryPoint,abs_of_nonneg hr] using hx
      · simp [highBoundaryPoint]
    rw [hz']
    exact he 1 (by norm_num) z.im hy
  · have hz' : z=highBoundaryPoint lam (-1) z.im := by
      apply Complex.ext
      · simp only [highBoundaryPoint,Complex.add_re,Complex.ofReal_re,Complex.mul_re,
          Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero,neg_mul,one_mul]
        rw [abs_of_neg (lt_of_not_ge hr)] at hx
        linarith
      · simp [highBoundaryPoint]
    rw [hz']
    exact he (-1) (by norm_num) z.im hy

end
end IsingBulk.Anisotropic
