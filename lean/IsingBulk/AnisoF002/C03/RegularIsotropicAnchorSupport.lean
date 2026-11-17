import IsingBulk.AnisoF002.C03.IsotropicAnchorPhysicalPeriodization
import IsingBulk.AnisoF002.C03.RegularIsotropicAnchoredDensity

/-!
# The same named compact-left gap on the full anchor support

The closed cosine inequality extends the literal nonzero-cutoff
inequality to its topological support. Every full transported descendant
is supported there, so all angular estimates retain the same anchor.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set

theorem actualLowerCompactAnchorCutoff_tsupport_cosine_gap {η b δ ρ : ℝ}
    (h : RightCutoffGeometry b δ ρ) (hη : 0 < η) (hρπ : ρ ≤ Real.pi / 2)
    (hgap : 2 * η ≤ Real.sin (ρ / 2)) (hbρ : b + δ / 2 + ρ < Real.pi)
    {N : ℕ} (a : Fin N) (θ : Fin N → ℝ)
    (hθ : θ ∈ tsupport (actualLowerCompactAnchorCutoff η b δ ρ a)) :
    Real.cos b - Real.cos (b + δ / 2) ≤ Real.cos b - Real.cos (θ a) := by
  let g := actualLowerCompactAnchorCutoff η b δ ρ a
  have hs : Function.support g ⊆
      {x | Real.cos b - Real.cos (b + δ / 2) ≤ Real.cos b - Real.cos (x a)} := by
    intro x hx
    have hj : iteratedFDeriv ℝ 0 g x ≠ 0 := by
      intro hz
      have hh : ‖iteratedFDeriv ℝ 0 g x‖ = ‖g x‖ := norm_iteratedFDeriv_zero
      rw [hz, norm_zero] at hh
      exact hx (norm_eq_zero.mp hh.symm)
    exact (actualLowerCompactAnchorCutoff_jet_cosine_gap h hη hρπ hgap hbρ a 0 x hj).2.2.2
  have hc : IsClosed {x : Fin N → ℝ |
      Real.cos b - Real.cos (b + δ / 2) ≤ Real.cos b - Real.cos (x a)} :=
    isClosed_le continuous_const (continuous_const.sub (Real.continuous_cos.comp (continuous_apply a)))
  exact closure_minimal hs hc hθ

theorem actual_anchor_cosine_constant_pos {b δ : ℝ} (hb : 0 < b) (hδ : 0 < δ)
    (hleft : b + δ < Real.pi) : 0 < Real.cos b - Real.cos (b + δ / 2) := by
  apply sub_pos.mpr
  exact Real.cos_lt_cos_of_nonneg_of_le_pi hb.le (by linarith only [hleft, hδ])
    (by linarith only [hδ])

end IsingBulk.AnisoF002.Isotropic
