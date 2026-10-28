import IsingBulk.HT22.PhysicalScope.RealSpin
import IsingBulk.HT.Final.Inversion

/-! Author-built controls, not an independent audit. These witnesses use the
actual extension predicates and actual published-real-temperature premise. -/
namespace IsingBulk.HT22.Controls
noncomputable section
open Set IsingBulk.HT22.PhysicalScope

/-- The actual exterior extension predicate accepts an entire constant. -/
theorem constant_has_exterior_extension (c z : ℂ) :
    IsingBulk.Final.HasExteriorExtension (fun _ : ℂ => c) z := by
  refine ⟨univ,isOpen_univ,mem_univ z,(fun _ => c),?_,?_⟩
  · intro t ht
    exact analyticAt_const
  · intro t ht
    rfl

/-- The actual punctured-interior overlap accepts the same entire constant. -/
theorem constant_has_interior_extension (c z : ℂ) :
    IsingBulk.HT.Final.HasInteriorExtension (fun _ : ℂ => c) z := by
  refine ⟨univ,isOpen_univ,mem_univ z,(fun _ => c),?_,?_⟩
  · intro t ht
    exact analyticAt_const
  · intro t ht
    rfl

/-- Hence a fake zero observable does not satisfy even the pointwise target. -/
theorem zero_not_natural_boundary :
    ¬(∀ z : ℂ, ‖z‖=1 →
      ¬IsingBulk.HT.Final.HasInteriorExtension (fun _ : ℂ => 0) z) := by
  intro h
  exact h 1 (by simp) (constant_has_interior_extension 0 1)

/-- Dropping the origin cannot satisfy the actual physical-input structure. -/
theorem omitted_origin_not_physical (corr : ℝ → LatticeSite → ℝ) :
    ¬PublishedRealHTSpinFormFactors
      (fun s v => if v=(0,0) then 0 else corr s v) := by
  intro h
  have hh := h.spin_square (1/2) (by norm_num) (by norm_num)
  norm_num at hh

/-- Zero correlations cannot be smuggled in as the real physical input. -/
theorem zero_not_physical :
    ¬PublishedRealHTSpinFormFactors (fun _ _ => 0) := by
  intro h
  have hh := h.spin_square (1/2) (by norm_num) (by norm_num)
  norm_num at hh

/-- The origin decomposition contains exactly the unit spin-square term. -/
theorem off_origin_bulk_differs_by_one {corr : ℝ → LatticeSite → ℝ}
    (hphys : PublishedRealHTSpinFormFactors corr) {s : ℝ} (hs : 0<s) (hs1 : s<1) :
    realBulk corr s-(∑' v : LatticeSite,if v=(0,0) then 0 else corr s v)=1 := by
  rw [realBulk_origin_add_offOrigin hphys hs hs1]
  ring

/-- In particular deleting the origin never leaves the actual full sum unchanged. -/
theorem off_origin_bulk_ne_full {corr : ℝ → LatticeSite → ℝ}
    (hphys : PublishedRealHTSpinFormFactors corr) {s : ℝ} (hs : 0<s) (hs1 : s<1) :
    (∑' v : LatticeSite,if v=(0,0) then 0 else corr s v)≠realBulk corr s := by
  intro h
  have hh := off_origin_bulk_differs_by_one hphys hs hs1
  rw [h,sub_self] at hh
  norm_num at hh

end
end IsingBulk.HT22.Controls
