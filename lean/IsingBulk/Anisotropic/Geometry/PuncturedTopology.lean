import IsingBulk.Anisotropic.Geometry.RegularEdges
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Perfect
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

namespace IsingBulk.Anisotropic
noncomputable section
open scoped Topology

theorem complex_punctured_ball_isPreconnected (z : ℂ) {r : ℝ} (hr : 0<r) :
    IsPreconnected (Metric.ball z r\{z}) := by
  let e := OpenPartialHomeomorph.univBall z r
  have hc : IsPreconnected ({0}ᶜ : Set ℂ) :=
    (isPathConnected_compl_singleton_of_one_lt_rank (by simp [Complex.rank_real_complex]) (0:ℂ)).isConnected.isPreconnected
  have he : e '' ({0}ᶜ : Set ℂ)=Metric.ball z r\{z} := by
    ext w
    constructor
    · rintro ⟨v,hv,rfl⟩
      refine ⟨?_,?_⟩
      · have hm := e.map_source (by simp [e] : v∈e.source)
        simpa [e,OpenPartialHomeomorph.univBall_target z hr] using hm
      · intro hw
        have hw' : e v=e 0 := by simpa [e] using hw
        exact hv (e.injOn (by simp [e]) (by simp [e]) hw')
    · rintro ⟨hw,hne⟩
      have hwt : w∈e.target := by simpa [e,OpenPartialHomeomorph.univBall_target z hr] using hw
      refine ⟨e.symm w,?_,e.right_inv hwt⟩
      intro hz
      have hz' : e.symm w=0 := hz
      have hi := e.right_inv hwt
      rw [hz'] at hi
      exact hne (by simpa [e] using hi.symm)
  rw [←he]
  exact hc.image e (OpenPartialHomeomorph.continuous_univBall z r).continuousOn

theorem frontier_preperfect_of_ambient_preperfect {s U : Set ℂ} (hs : Preperfect s)
    (hU : IsOpen U) (hsub : U⊆sᶜ) (hfront : frontier U⊆s) : Preperfect (frontier U) := by
  rw [preperfect_iff_nhds]
  intro z hz N hN
  by_contra hn
  push Not at hn
  rcases Metric.mem_nhds_iff.mp hN with ⟨r,hr,hrN⟩
  have hfrontonly : ∀w∈Metric.ball z r, w∈frontier U → w=z := by
    intro w hw hwf
    exact hn w ⟨hrN hw,hwf⟩
  have hbU : Metric.ball z r\{z} ⊆ U := by
    apply (complex_punctured_ball_isPreconnected z hr).subset_of_closure_inter_subset hU
    · rcases mem_closure_iff.mp (frontier_subset_closure hz) _ Metric.isOpen_ball
        (Metric.mem_ball_self hr) with ⟨w,hw,hwU⟩
      refine ⟨w,⟨hw,?_⟩,hwU⟩
      intro he
      have hzn : z∉U := by rw [hU.frontier_eq] at hz; exact hz.2
      exact hzn (he ▸ hwU)
    · rintro w ⟨hwcl,hwball,hwne⟩
      by_contra hwU
      have hwf : w∈frontier U := by rw [hU.frontier_eq]; exact ⟨hwcl,hwU⟩
      exact hwne (hfrontonly w hwball hwf)
  rcases preperfect_iff_nhds.mp hs z (hfront hz) _ (Metric.ball_mem_nhds z hr) with ⟨w,⟨hw,hsw⟩,hne⟩
  exact hsub (hbU ⟨hw,hne⟩) hsw

theorem LocallyFiniteSubset.eventually_avoids {E : Set ℂ} (hE : LocallyFiniteSubset E) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, w∉E := by
  rcases hE z with ⟨U,hU,hz,hfin⟩
  have hav : ∀ᶠ w in 𝓝[≠] z, w∉E∩U := (nhdsNE_le_cofinite z) hfin.compl_mem_cofinite
  have hu : ∀ᶠ w in 𝓝[≠] z, w∈U := nhdsWithin_le_nhds (hU.mem_nhds hz)
  filter_upwards [hav,hu] with w hw hwu
  exact fun hwe => hw ⟨hwe,hwu⟩

theorem Preperfect.subset_closure_diff_locallyFinite {s E : Set ℂ} (hs : Preperfect s)
    (hE : LocallyFiniteSubset E) : s⊆closure (s\E) := by
  intro z hz
  apply mem_closure_iff.mpr
  intro U hU hzU
  have he := hE.eventually_avoids z
  rw [nhdsWithin,Filter.eventually_inf_principal] at he
  have hN : {w | w∈U ∧ (w≠z → w∉E)}∈𝓝 z := Filter.inter_mem (hU.mem_nhds hzU) he
  rcases preperfect_iff_nhds.mp hs z hz _ hN with ⟨w,⟨⟨hwU,hwE⟩,hws⟩,hwne⟩
  exact ⟨w,hwU,hws,hwE hwne⟩

end
end IsingBulk.Anisotropic
