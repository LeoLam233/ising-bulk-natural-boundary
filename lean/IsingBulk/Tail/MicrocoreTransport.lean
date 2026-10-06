import IsingBulk.Analysis.JetsPullback

/-! The actual one-phase microcore field. It freezes every regular branch
coordinate, hence any analytic polynomial or simple Z kernel in those
coordinates. No selected-difference denominator is introduced. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets IsingBulk.Lie
open scoped BigOperators

def microcoreField {n : ℕ} (v θ : ℝ) (s : ℂ) (x : AngularSpace n) (i : Fin (n+1)) : ℂ :=
  chartA s v θ (x i)

theorem microcore_field_freezes_coordinate (s : ℂ) (v θ : ℝ) (u : ℂ)
    (hg : angularG v θ u ≠ 0) :
    chartTau s v θ u-chartA s v θ u*chartB s v θ u=0 := by
  rw [mul_comm (chartA _ _ _ _),chartB_mul_chartA s v θ u hg]
  simp [chartTau]

theorem microcore_transport_chain {n : ℕ} (v θ : ℝ) (s : ℂ) (x : AngularSpace n)
    (F : ℂ → (Fin (n+1) → ℂ) → ℂ) (hs : s ≠ 0)
    (hr : ∀ i, 0 < (chartW s v θ (x i)).re)
    (hi : ∀ i, 0 < (chartW s v θ (x i)).im)
    (hg : ∀ i, angularG v θ (x i) ≠ 0)
    (hF : DifferentiableAt ℂ (fun z : ℂ × (Fin (n+1) → ℂ) => F z.1 z.2)
      (s,chartMap v θ s x)) :
    transport (microcoreField v θ) (fun t y => F t (chartMap v θ t y)) s x =
      deriv (fun t => F t (chartMap v θ s x)) s := by
  have hparam := hF.hasFDerivAt.comp_hasDerivAt s
    ((hasDerivAt_id s).prodMk (hasDerivAt_const s (chartMap v θ s x)))
  change HasDerivAt (fun t => F t (chartMap v θ s x))
    (fderiv ℂ (fun z : ℂ × (Fin (n+1) → ℂ) => F z.1 z.2) (s,chartMap v θ s x) (1,0)) s at hparam
  rw [hparam.deriv]
  unfold transport
  rw [chart_composition_parameter v θ s x F hs hr hi hF]
  simp_rw [chart_composition_spatial v θ s x F hr hi hF]
  let L := fderiv ℂ (fun z : ℂ × (Fin (n+1) → ℂ) => F z.1 z.2) (s,chartMap v θ s x)
  change L (1,fun i => chartTau s v θ (x i))-
    (∑ i, microcoreField v θ s x i*L (0,Pi.single i (chartB s v θ (x i)))) = L (1,0)
  simp_rw [← smul_eq_mul,← map_smul]
  rw [← map_sum,← map_sub]
  congr 1
  apply Prod.ext
  · change (1:ℂ)-(ContinuousLinearMap.fst ℂ ℂ (Fin (n+1) → ℂ))
      (∑ i, microcoreField v θ s x i • (0,Pi.single i (chartB s v θ (x i))))=1
    rw [map_sum]
    simp
  · change (fun i => chartTau s v θ (x i))-
      (ContinuousLinearMap.snd ℂ ℂ (Fin (n+1) → ℂ))
        (∑ i, microcoreField v θ s x i • (0,Pi.single i (chartB s v θ (x i))))=0
    rw [map_sum]
    funext i
    simp only [Pi.sub_apply,Pi.zero_apply,Finset.sum_apply,map_smul]
    simp [Pi.single_apply,microcoreField,microcore_field_freezes_coordinate s v θ (x i) (hg i)]

/-- Every analytic fixed-regular-coordinate observable is frozen, not merely
its value at the radial center. -/
theorem microcore_transport_fixed_observable {n : ℕ} (v θ : ℝ) (s : ℂ) (x : AngularSpace n)
    (Q : (Fin (n+1) → ℂ) → ℂ) (hs : s ≠ 0)
    (hr : ∀ i, 0 < (chartW s v θ (x i)).re)
    (hi : ∀ i, 0 < (chartW s v θ (x i)).im)
    (hg : ∀ i, angularG v θ (x i) ≠ 0)
    (hQ : DifferentiableAt ℂ Q (chartMap v θ s x)) :
    transport (microcoreField v θ) (fun t y => Q (chartMap v θ t y)) s x=0 := by
  have hh := microcore_transport_chain v θ s x (fun _ φ => Q φ) hs hr hi hg
    (hQ.comp (s,chartMap v θ s x) differentiableAt_snd)
  simpa using hh

def microcoreVandermondeSquared {N : ℕ} (φ : Fin N → ℂ) : ℂ :=
  ∏ i, ∏ j ∈ Finset.univ.filter (fun j => i<j), (φ i-φ j)^2

theorem microcoreVandermondeSquared_differentiable (N : ℕ) :
    Differentiable ℂ (@microcoreVandermondeSquared N) := by
  unfold microcoreVandermondeSquared
  fun_prop

/-- The full collision polynomial is unchanged by the source microcore field. -/
theorem microcore_vandermonde_frozen {n : ℕ} (v θ : ℝ) (s : ℂ) (x : AngularSpace n)
    (hs : s ≠ 0) (hr : ∀ i, 0 < (chartW s v θ (x i)).re)
    (hi : ∀ i, 0 < (chartW s v θ (x i)).im)
    (hg : ∀ i, angularG v θ (x i) ≠ 0) :
    transport (microcoreField v θ)
      (fun t y => microcoreVandermondeSquared (chartMap v θ t y)) s x=0 :=
  microcore_transport_fixed_observable v θ s x _ hs hr hi hg
    (microcoreVandermondeSquared_differentiable (n+1) _)

end
end IsingBulk.Tail
