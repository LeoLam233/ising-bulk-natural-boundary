import IsingBulk.Anisotropic.Geometry.ComponentDensity
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Complex.Convex

namespace IsingBulk.Anisotropic
noncomputable section
open scoped Topology

/-- A genuine nonramified analytic half-plane coordinate parametrizes the frontier of the
same complement component, not just an unspecified nearby component. -/
theorem exists_same_component_frontier_chart {s : Set ℂ} (hs : IsClosed s) (a : ℂ)
    {z : ℂ} (hz : z∈frontier (connectedComponentIn sᶜ a)) {f : ℂ→ℂ}
    (hf : AnalyticAt ℂ f z) (hd : deriv f z≠0)
    (hside : ∀ᶠ w in 𝓝 z, w∈s ↔ (f w).im≤0) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, (e : ℂ→ℂ)=f ∧ z∈e.source ∧
      ∃r : ℝ, 0<r ∧ Metric.ball (f z) r⊆e.target ∧
        ∀w∈Metric.ball (f z) r, w.im=0 → e.symm w∈frontier (connectedComponentIn sᶜ a) := by
  let i := ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 (deriv f z) hd)
  have hfd : HasStrictFDerivAt f (i : ℂ→L[ℂ] ℂ) z :=
    hf.hasStrictDerivAt.hasStrictFDerivAt_equiv hd
  let e := hfd.toOpenPartialHomeomorph f
  have hzsource : z∈e.source := hfd.mem_toOpenPartialHomeomorph_source
  have he : (e : ℂ→ℂ)=f := rfl
  have hside' : ∀ᶠ w in 𝓝 (f z), w∈e.target ∧ (e.symm w∈s ↔ w.im≤0) := by
    have ht := e.open_target.mem_nhds (e.map_source hzsource)
    have hv := (e.tendsto_symm hzsource) hside
    filter_upwards [ht,hv] with w hwt hw
    refine ⟨hwt,?_⟩
    change (e.symm w∈s ↔ (f (e.symm w)).im≤0) at hw
    simpa only [←he,e.right_inv hwt] using hw
  rcases Metric.mem_nhds_iff.mp hside' with ⟨r,hr,hrprop⟩
  have hrt : Metric.ball (f z) r⊆e.target := fun w hw => (hrprop hw).1
  let H : Set ℂ := Metric.ball (f z) r∩{w | 0<w.im}
  have hH : IsPreconnected H := ((convex_ball (f z) r).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hHtarget : H⊆e.target := fun w hw => hrt hw.1
  have hpre : IsPreconnected (e.symm '' H) := hH.image e.symm (e.symm.continuousOn.mono hHtarget)
  have hcompl : e.symm '' H⊆sᶜ := by
    rintro w ⟨v,hv,rfl⟩ hws
    exact (not_le_of_gt hv.2) ((hrprop hv.1).2.mp hws)
  have hWopen : IsOpen (e.source∩e ⁻¹' Metric.ball (f z) r) := e.isOpen_inter_preimage Metric.isOpen_ball
  have hzW : z∈e.source∩e ⁻¹' Metric.ball (f z) r := ⟨hzsource,Metric.mem_ball_self hr⟩
  rcases mem_closure_iff.mp (frontier_subset_closure hz) _ hWopen hzW with ⟨v,hvW,hvcomp⟩
  have hvH : v∈e.symm '' H := by
    refine ⟨e v,⟨hvW.2,?_⟩,e.left_inv hvW.1⟩
    have hn : v∉s := connectedComponentIn_subset _ _ hvcomp
    have hvside := (hrprop hvW.2).2
    rw [e.left_inv hvW.1] at hvside
    exact lt_of_not_ge (fun h => hn (hvside.mpr h))
  have hsub : e.symm '' H⊆connectedComponentIn sᶜ a := by
    rw [connectedComponentIn_eq hvcomp]
    exact hpre.subset_connectedComponentIn hvH hcompl
  refine ⟨e,he,hzsource,r,hr,hrt,?_⟩
  intro w hw hwi
  have hwcl : w∈closure H := by
    apply Metric.isOpen_ball.inter_closure
    refine ⟨hw,?_⟩
    rw [Complex.closure_setOfPred_lt_im]
    change 0≤w.im
    rw [hwi]
  have himg : e.symm w∈closure (e.symm '' H) := mem_closure_image (e.continuousAt_symm (hrt hw)) hwcl
  rw [hs.isOpen_compl.connectedComponentIn.frontier_eq]
  refine ⟨closure_mono hsub himg,?_⟩
  intro hc
  exact connectedComponentIn_subset _ _ hc ((hrprop hw).2.mpr (hwi.symm ▸ le_refl 0))

end
end IsingBulk.Anisotropic
