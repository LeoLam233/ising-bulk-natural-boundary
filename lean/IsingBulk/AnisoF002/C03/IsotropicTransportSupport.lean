import IsingBulk.AnisoF002.C03.IsotropicActualWordGerms
import IsingBulk.AnisoF002.C03.IsotropicCompactRightCutoff

/-!
# The complete transport recurrence does not enlarge cutoff support

This is a locality theorem for the actual differential operator. It
requires no nonsingularity assumption outside the support: a zero germ
remains zero under the literal full recurrence at every order.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter
open scoped Topology BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem regularTransportAmplitude_zero_amplitude (χ : ι → E → ℂ) (e : ι → E)
    (a : E) (B : ι → E → ℂ) : regularTransportAmplitude χ e a B (fun _ => 0) = fun _ => 0 := by
  funext x
  simp [regularTransportAmplitude, scalarRegularParameterDerivative, scalarFrameParameter,
    scalarRegularFrameDerivative, scalarFrameApplied, scalarPartial]

theorem regularTransportDescendant_zero_amplitude (χ : ι → E → ℂ) (e : ι → E)
    (a : E) (B : ι → E → ℂ) (n : ℕ) :
    regularTransportDescendant χ e a B (fun _ => 0) n = fun _ => 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [regularTransportDescendant, ih, regularTransportAmplitude_zero_amplitude]

theorem regularTransportDescendant_congr_germ (χ : ι → E → ℂ) (e : ι → E)
    (a : E) (B : ι → E → ℂ) (f g : E → ℂ) (x : E)
    (hfg : f =ᶠ[𝓝 x] g) (n : ℕ) :
    regularTransportDescendant χ e a B f n x = regularTransportDescendant χ e a B g n x := by
  induction n generalizing x with
  | zero => exact hfg.eq_of_nhds
  | succ n ih =>
    have he : regularTransportDescendant χ e a B f n =ᶠ[𝓝 x]
        regularTransportDescendant χ e a B g n := by
      filter_upwards [eventually_eventuallyEq_nhds.mpr hfg] with y hy
      exact ih y hy
    exact regularTransportAmplitude_congr_germ χ e a x B _ _ he

theorem regularTransportDescendant_tsupport (χ : ι → E → ℂ) (e : ι → E)
    (a : E) (B : ι → E → ℂ) (f : E → ℂ) (n : ℕ) :
    tsupport (regularTransportDescendant χ e a B f n) ⊆ tsupport f := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hf
  have hz : f =ᶠ[𝓝 x] (fun _ => 0) := notMem_tsupport_iff_eventuallyEq.mp hf
  have he := regularTransportDescendant_congr_germ χ e a B f (fun _ => 0) x hz n
  rw [regularTransportDescendant_zero_amplitude] at he
  exact hx he

theorem actualTransportDescendant_cutoff_tsupport {N : ℕ} (η τ ξ : ℝ)
    (g : (Fin N → ℝ) → ℂ) (n : ℕ) :
    tsupport (actualTransportDescendant η τ ξ
      (actualInitialAmplitude η τ ξ (fun x => g x.2)) n) ⊆
      Prod.snd ⁻¹' tsupport g := by
  apply (regularTransportDescendant_tsupport (actualPhysicalCoordinate η τ ξ) actualAngularDirection
    actualTimeDirection (actualCovarianceRegularField η τ ξ) _ n).trans
  apply closure_minimal
  · intro x hx
    have hg : g x.2 ≠ 0 := by
      intro hz
      apply hx
      change isotropicParticleNormalization N * g x.2 * actualRegularNumerator η τ ξ x = 0
      rw [hz, mul_zero, zero_mul]
    exact subset_closure hg
  · exact isClosed_closure.preimage continuous_snd

theorem actual_compact_right_descendant_all_jet_support {N : ℕ} {b δ ρ : ℝ}
    (h : RightCutoffGeometry b δ ρ) (η τ ξ : ℝ) (n k : ℕ)
    (x : ℂ × (Fin N → ℝ))
    (hne : iteratedFDeriv ℝ k (actualTransportDescendant η τ ξ
      (actualInitialAmplitude η τ ξ (fun y => actualLowerCompactRightCutoff η b δ ρ N y.2)) n) x ≠ 0) :
    ∀ i, x.2 i ∈ Icc (-b - δ) (ρ + δ / 2) := by
  have hs := actualTransportDescendant_cutoff_tsupport η τ ξ
    (actualLowerCompactRightCutoff η b δ ρ N) n (support_iteratedFDeriv_subset k hne)
  exact compactRightProduct_weighted_tsupport h
    (fun θ : Fin N → ℝ => (lowerPopulationCutoff η θ : ℂ)) hs

end
end IsingBulk.AnisoF002.Isotropic
