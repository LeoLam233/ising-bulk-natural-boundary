import IsingBulk.AnisoF002.C03.IsotropicTransportDensity

/-!
# Exact zero current outside the actual smooth cutoff support

No covariance regularity is needed outside the cutoff. Locality of the
literal full recurrence makes every density and flux germ zero there,
including every first derivative used by the integrated current.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter
open scoped Topology BigOperators ContDiff

variable {N : ℕ}

theorem actualTransportedDensity_outside_smooth (σ : ℂ) (η τ ξ : ℝ)
    (g : (Fin N → ℝ) → ℂ) (j : ℕ) (q : ℂ × (Fin N → ℝ)) (hq : q.2 ∉ tsupport g) :
    ContDiffAt ℝ ∞ (actualTransportedDensity σ η τ ξ g j) q ∧
      AnalyticAt ℂ (fun s => actualTransportedDensity σ η τ ξ g j (s, q.2)) q.1 := by
  have hz := actualTransportedDensity_zero_germ σ η τ ξ g j q hq
  refine ⟨contDiffAt_const.congr_of_eventuallyEq hz, ?_⟩
  have hmap : ContinuousAt (fun s : ℂ => (s, q.2)) q.1 := continuousAt_id.prodMk continuousAt_const
  have he : (fun s => actualTransportedDensity σ η τ ξ g j (s, q.2)) =ᶠ[𝓝 q.1] (fun _ => 0) :=
    hmap.eventually hz
  exact analyticAt_const.congr he.symm

theorem actualTransportedFlux_outside_smooth (σ : ℂ) (η τ ξ : ℝ)
    (g : (Fin N → ℝ) → ℂ) (j : ℕ) (i : Fin N)
    (q : ℂ × (Fin N → ℝ)) (hq : q.2 ∉ tsupport g) :
    ContDiffAt ℝ ∞ (actualTransportedFlux σ η τ ξ g j i) q :=
  contDiffAt_const.congr_of_eventuallyEq (actualTransportedFlux_zero_germ σ η τ ξ g j i q hq)

theorem actualTransportedCurrent_outside (σ : ℂ) (η τ ξ : ℝ)
    (g : (Fin N → ℝ) → ℂ) (j : ℕ) (q : ℂ × (Fin N → ℝ)) (hq : q.2 ∉ tsupport g)
    (anchor : Fin N) :
    scalarPartial (actualTransportedDensity σ η τ ξ g j) actualTimeDirection q -
      (∑ k ∈ Finset.univ.erase anchor, scalarPartial (actualTransportedFlux σ η τ ξ g j k)
        (actualAngularDirection k - actualAngularDirection anchor) q) =
      actualTransportedDensity σ η τ ξ g (j + 1) q := by
  have hd := actualTransportedDensity_zero_germ σ η τ ξ g j q hq
  have hn := actualTransportedDensity_zero_germ σ η τ ξ g (j + 1) q hq
  have hf (k : Fin N) := actualTransportedFlux_zero_germ σ η τ ξ g j k q hq
  unfold scalarPartial
  rw [hd.fderiv_eq, fderiv_const_apply, zero_apply, hn.eq_of_nhds]
  simp only [(hf _).fderiv_eq, fderiv_const_apply, zero_apply, Finset.sum_const_zero, sub_zero]

end
end IsingBulk.AnisoF002.Isotropic
