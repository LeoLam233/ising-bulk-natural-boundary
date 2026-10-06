import IsingBulk.Tail.CompactSelectedLieDensity
import IsingBulk.Tail.CompactDividedDeterminant

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter
open scoped Topology
set_option maxHeartbeats 1600000

/-- The source curvature theorem supplies the selected determinant margin
uniformly in the whole intermediate window. The only excluded points are
the selected diagonal itself; no unproved determinant bound is an input. -/
theorem actual_compact_selected_window (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) (f : SelectorFunctions) (hf : RegularSelector f)
    (hp1 : ∀ x, f.p x ≤ 1) {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ < 2*(1-Real.cos d.thetaB))
    {D β : ℝ} (hD : 0 ≤ D) (hβ : 0 < β) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ H : ℝ in atTop, ∀ N : ℕ, 0 < N → (N:ℝ) ≤ D*Real.sqrt H →
      ∀ τ lam : ℝ, 0 ≤ τ → τ ≤ 1 → 0 ≤ lam → lam ≤ Real.exp (-β*H) →
      ∀ i j : Fin N, i ≠ j → ∀ θ : Fin N → ℝ,
      (∀ l, θ l ∈ Icc (-rightSectorRadius d.thetaB δ) (rightSectorRadius d.thetaB δ)) →
      let r := Real.exp (-d.c₀*Real.exp (-H))
      let s := radialParameter d.theta (Real.exp (-H))
      c*|θ i-θ j| ≤ ‖currentAngularDeterminant f r τ lam s i j θ‖ ∧
      (θ i ≠ θ j → (s,θ) ∈ compactSelectedDomain f r τ lam i j) := by
  obtain ⟨c,hc,hmargin⟩ := actual_current_divided_determinant d hcsmall f hf hp1 hδ hδsmall hD hβ
  refine ⟨c,hc,?_⟩
  have ht : Tendsto (fun H : ℝ => Real.exp (-H)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨Real.tendsto_exp_neg_atTop_nhds_zero,
      Eventually.of_forall (fun H => Real.exp_pos (-H))⟩
  filter_upwards [hmargin,ht.eventually (radial_source_eventually_damping d hcsmall)] with H hm hdom
  intro N hN hND τ lam hτ hτ1 hlam hlamB i j hij θ hθ
  have hh := hm N hN hND τ lam hτ hτ1 hlam hlamB i j hij
  have hbound := hh.2.2 θ hθ
  have hnorm : c*|θ i-θ j| ≤ ‖currentAngularDeterminant f
      (Real.exp (-d.c₀*Real.exp (-H))) τ lam (radialParameter d.theta (Real.exp (-H))) i j θ‖ := by
    rw [hh.2.1 θ,norm_smul,Real.norm_eq_abs]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hbound (abs_nonneg (θ i-θ j))
  refine ⟨hnorm,?_⟩
  intro hne
  refine ⟨⟨hdom.2.2,mem_univ _⟩,?_⟩
  exact norm_pos_iff.mp ((mul_pos hc (abs_pos.mpr (sub_ne_zero.mpr hne))).trans_le hnorm)

end
end IsingBulk.Tail
