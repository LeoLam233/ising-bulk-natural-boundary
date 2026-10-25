import IsingBulk.Anisotropic.Final.AnalyticInverse
import Mathlib.Topology.Homeomorph.Lemmas

namespace IsingBulk.Joint
noncomputable section
open Set Filter
open scoped Topology

theorem analytic_bijOn_isOpenMap {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    {f : ℂ → ℂ} (hb : Set.BijOn f U V) (hf : AnalyticOnNhd ℂ f U)
    (hd : ∀ z ∈ U, deriv f z ≠ 0) : IsOpenMap (hb.equiv f) := by
  apply hV.isOpenEmbedding_subtypeVal.isOpenMap_iff.mpr
  intro W hW
  have hWo : IsOpen (Subtype.val '' W : Set ℂ) := hU.isOpenMap_subtype_val W hW
  have himage : (Subtype.val ∘ hb.equiv f) '' W = f '' (Subtype.val '' W) := by
    ext y
    simp only [Set.mem_image, Function.comp_apply]
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨x,⟨x,hx,rfl⟩,rfl⟩
    · rintro ⟨x,⟨a,ha,rfl⟩,rfl⟩
      exact ⟨a,ha,rfl⟩
  rw [himage]
  apply isOpen_iff_mem_nhds.mpr
  rintro y ⟨z,hz,rfl⟩
  obtain ⟨a,ha,rfl⟩ := hz
  have he := (hf a a.property).hasStrictDerivAt.map_nhds_eq (hd a a.property)
  rw [← he]
  exact image_mem_map (hWo.mem_nhds ⟨a,ha,rfl⟩)

/-- Actual topological and analytic inverse data, derived from a bijection and
nonvanishing derivative, not supplied as a continuation hypothesis. -/
def analyticBijOnHomeomorph {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    {f : ℂ → ℂ} (hb : Set.BijOn f U V) (hf : AnalyticOnNhd ℂ f U)
    (hd : ∀ z ∈ U, deriv f z ≠ 0) : U ≃ₜ V :=
  (hb.equiv f).toHomeomorphOfContinuousOpen
    (by
      apply Continuous.subtype_mk
      exact hf.continuousOn.domRestrict)
    (analytic_bijOn_isOpenMap hU hV hb hf hd)

end
end IsingBulk.Joint
