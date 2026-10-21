import IsingBulk.Final.AnalyticFactorTransfer

/-! Exact inversion of genuine local extensions. The domain is the punctured
unit disk because t=1/s is used here; at a unit-circle point this is the same
local continuation question as for the disk. No natural-boundary premise is
invented or discharged by these general transport lemmas. -/
namespace IsingBulk.HT.Final
noncomputable section
open Set Filter IsingBulk.Final
open scoped Topology

/-- A holomorphic extension agreeing with the actual interior germ on an open
overlap. The function is not defined by a singularity or by a desired theorem. -/
def HasInteriorExtension (f : ℂ → ℂ) (z : ℂ) : Prop :=
  ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧ ∃ g : ℂ → ℂ,
    AnalyticOnNhd ℂ g U ∧ EqOn g f (U ∩ {s : ℂ | 0 < ‖s‖ ∧ ‖s‖ < 1})

theorem exterior_extension_of_interior_inversion {f : ℂ → ℂ} {z : ℂ}
    (hz : z ≠ 0) (he : HasInteriorExtension (fun s => f (s⁻¹)) z⁻¹) :
    HasExteriorExtension f z := by
  obtain ⟨U,hU,hzU,g,hg,hEq⟩ := he
  let V : Set ℂ := {t | t ≠ 0 ∧ t⁻¹ ∈ U}
  have hV : IsOpen V := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    have hn : ∀ᶠ u : ℂ in 𝓝 t, u ≠ 0 :=
      (isOpen_ne : IsOpen {u : ℂ | u ≠ 0}).mem_nhds ht.1
    have hi : ∀ᶠ u : ℂ in 𝓝 t, u⁻¹ ∈ U :=
      (continuousAt_id.inv₀ ht.1).eventually (hU.mem_nhds ht.2)
    exact hn.and hi
  refine ⟨V,hV,⟨hz,hzU⟩,(fun t => g (t⁻¹)),?_,?_⟩
  · intro t ht
    exact (hg (t⁻¹) ht.2).comp (analyticAt_id.inv ht.1)
  · intro t ht
    have hp : 0 < ‖t⁻¹‖ := norm_pos_iff.mpr (inv_ne_zero ht.1.1)
    have hl : ‖t⁻¹‖ < 1 := by
      rw [norm_inv]
      exact inv_lt_one_of_one_lt₀ ht.2
    simpa only [inv_inv] using hEq ⟨ht.1.2,hp,hl⟩

theorem no_interior_extension_of_exterior_nonextension {f : ℂ → ℂ} {z : ℂ}
    (hz : z ≠ 0) (hf : ¬ HasExteriorExtension f z) :
    ¬ HasInteriorExtension (fun s => f (s⁻¹)) z⁻¹ :=
  fun he => hf (exterior_extension_of_interior_inversion hz he)

/-- Inversion transfers a fully proved exterior natural boundary. This is a
conditional transport theorem, not the HT natural-boundary endpoint. -/
theorem inversion_transfers_natural_boundary {f : ℂ → ℂ}
    (hf : ∀ z : ℂ, ‖z‖=1 → ¬ HasExteriorExtension f z) :
    ∀ z : ℂ, ‖z‖=1 → ¬ HasInteriorExtension (fun s => f (s⁻¹)) z := by
  intro z hz
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hz]; norm_num)
  have hi : ‖z⁻¹‖=1 := by rw [norm_inv,hz]; norm_num
  simpa only [inv_inv] using
    no_interior_extension_of_exterior_nonextension (inv_ne_zero hz0) (hf (z⁻¹) hi)

end
end IsingBulk.HT.Final
