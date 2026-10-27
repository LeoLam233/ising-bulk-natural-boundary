import IsingBulk.Preferred22.AnchorGeometry

/-! Exact support of every literal named-anchor descendant. All vanishing
is established on real open angular neighborhoods before differentiation. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

theorem preferredTransportedDensity_anchor_support {N : ℕ}
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB : ℝ}
    (a : Fin N) (τ : ℝ) (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (j : ℕ) (s : ℂ) (θ : Fin N → ℝ)
    (hθ : ∀ i,θ i∈Ioc (-Real.pi-B.delta) (Real.pi-B.delta))
    (houtside : ¬((∀ i,θ i∈Icc (-Real.pi-B.delta) B.delta) ∧ θ a≤ -d.b-δB/2)) :
    preferredTransportedDensity (.anchor a) τ preferredPopulationCutoff B.p B.m rcut j s θ=0 := by
  classical
  by_cases hcore : ∀ i,θ i∈Icc (-Real.pi-B.delta) B.delta
  · have ha : -d.b-δB/2<θ a := lt_of_not_ge (fun h => houtside ⟨hcore,h⟩)
    by_cases htop : θ a<B.delta
    · let U : Set (Fin N → ℝ) := (fun x => x a) ⁻¹' Ioo
        (max (-Real.pi-B.delta) (-d.b-δB/2)) B.delta
      have hU : IsOpen U := isOpen_Ioo.preimage (continuous_apply a)
      have hz : θ∈U := ⟨max_lt (hθ a).1 ha,htop⟩
      apply preferredTransportedDensity_zero_on_open (.anchor a) τ preferredPopulationCutoff B.p B.m rcut U hU _ j s θ hz
      intro t x hx
      have hxl : -Real.pi-B.delta<x a := (le_max_left _ _).trans_lt hx.1
      have hxa : -d.b-δB/2<x a := (le_max_right _ _).trans_lt hx.1
      have hrone : rcut (x a)=1 := (hcut.2.2.2.2.2 (x a) ⟨hxl.le,hx.2.le⟩).2 (by linarith)
      simp only [preferredPhysicalSeed,preferredCellWeight,preferredAnchorWeight,hrone,sub_self,zero_mul,mul_zero,
        Complex.ofReal_zero,zero_div]
    · have hp : 1/2<B.p (θ a) := by
        rw [B.plateau (θ a) ⟨(le_of_not_gt htop),(hθ a).2⟩]
        norm_num
      exact preferredTransportedDensity_cell_zero_of_upper_particle (.anchor a) d B τ rcut j s θ a hp
  · obtain ⟨i,hi⟩ := not_forall.mp hcore
    have htop : B.delta<θ i := by
      apply lt_of_not_ge
      intro hh
      exact hi ⟨(hθ i).1.le,hh⟩
    have hp : 1/2<B.p (θ i) := by rw [B.plateau (θ i) ⟨htop.le,(hθ i).2⟩]; norm_num
    exact preferredTransportedDensity_cell_zero_of_upper_particle (.anchor a) d B τ rcut j s θ i hp

end
end IsingBulk.Preferred22
