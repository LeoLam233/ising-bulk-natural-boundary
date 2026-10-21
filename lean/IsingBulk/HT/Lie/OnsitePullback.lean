import IsingBulk.HT.Lie.OnsiteVolume
import IsingBulk.Tail.MicrocoreWeightedStep

/-! Onsite top-form and real-cutoff recurrence. The volume cancellation
and zero residual are established from the genuine coupled contour. -/
namespace IsingBulk.HT.Lie
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail IsingBulk.Lie Set Filter
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem onsite_volume_lie_zero {n : ℕ}
    (J : Finset (Fin (n+1))) (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (θ : Fin (n+1) → ℝ) (hs : s≠0)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hplateau : ∀ i∈J,deriv f.p (θ i)=0 ∧ deriv f.m (θ i)=0)
    (hW : ∀ i∈J,0<(sourceW s (deformedPoint f r τ lam θ i)).im)
    (hg : ∀ i∈J,deformedPoint f r τ lam θ i-(deformedPoint f r τ lam θ i)⁻¹≠0) :
    lieStep (onsiteBranchField J f r τ lam) (mixedHybridVolume J f r τ lam) s θ=0 := by
  rw [← mixedCoordinateLie_eq_lie]
  · exact onsite_volume_coordinate_lie_zero J f hr τ lam s θ hs hp hm hplateau hW hg
  · intro i
    exact (onsiteBranchField_spatial_differentiable J f hr τ lam s θ hp hm hg i).mul
      (mixedHybridVolume_spatial_differentiable J f hr τ lam s θ hp hm hW)

def onsiteHybridPullback {N : ℕ} (J : Finset (Fin N)) (f : SelectorFunctions)
    (r τ lam : ℝ) (F : ℂ → (Fin N → ℂ) → ℂ) (s : ℂ) (θ : Fin N → ℝ) : ℂ :=
  mixedHybridVolume J f r τ lam s θ*F s (mixedHybridMap J f r τ lam s θ)

theorem onsiteHybridPullback_differentiable {N : ℕ}
    (J : Finset (Fin N)) (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (hs : s≠0)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hW : ∀ i∈J,0<(sourceW s (deformedPoint f r τ lam θ i)).im)
    (F : ℂ → (Fin N → ℂ) → ℂ)
    (hF : DifferentiableAt ℂ (fun z : ℂ × (Fin N → ℂ) => F z.1 z.2)
      (s,mixedHybridMap J f r τ lam s θ)) :
    DifferentiableAt ℂ (fun t => onsiteHybridPullback J f r τ lam F t θ) s ∧
    DifferentiableAt ℝ (onsiteHybridPullback J f r τ lam F s) θ := by
  have hAs : DifferentiableAt ℂ (fun t => F t (mixedHybridMap J f r τ lam t θ)) s := by
    convert (hF.hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (mixedHybridMap_parameter J f r τ lam s θ hs hW))).differentiableAt using 1
    rfl
  have hAx : DifferentiableAt ℝ (fun x => F s (mixedHybridMap J f r τ lam s x)) θ := by
    convert ((hF.restrictScalars ℝ).comp θ ((differentiableAt_const s).prodMk
      (mixedHybridMap_spatial_differentiable J f hr τ lam s θ hp hm hW))) using 1
    rfl
  exact ⟨(mixedHybridVolume_parameter J f r τ lam s θ hs hW).differentiableAt.mul hAs,
    (mixedHybridVolume_spatial_differentiable J f hr τ lam s θ hp hm hW).mul hAx⟩

/-- The top-form step contains only explicit parameter differentiation. -/
theorem onsiteHybridPullback_lie {n : ℕ}
    (J : Finset (Fin (n+1))) (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (θ : Fin (n+1) → ℝ) (hs : s≠0)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hplateau : ∀ i∈J,deriv f.p (θ i)=0 ∧ deriv f.m (θ i)=0)
    (hW : ∀ i∈J,0<(sourceW s (deformedPoint f r τ lam θ i)).im)
    (hg : ∀ i∈J,deformedPoint f r τ lam θ i-(deformedPoint f r τ lam θ i)⁻¹≠0)
    (F : ℂ → (Fin (n+1) → ℂ) → ℂ)
    (hF : DifferentiableAt ℂ (fun z : ℂ × (Fin (n+1) → ℂ) => F z.1 z.2)
      (s,mixedHybridMap J f r τ lam s θ)) :
    lieStep (onsiteBranchField J f r τ lam) (onsiteHybridPullback J f r τ lam F) s θ =
      onsiteHybridPullback J f r τ lam (fun t φ => deriv (fun z => F z φ) t) s θ := by
  let A := fun t x => F t (mixedHybridMap J f r τ lam t x)
  have hAs : DifferentiableAt ℂ (fun t => A t θ) s := by
    convert (hF.hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (mixedHybridMap_parameter J f r τ lam s θ hs hW))).differentiableAt using 1
    rfl
  have hAx : DifferentiableAt ℝ (A s) θ := by
    convert ((hF.restrictScalars ℝ).comp θ ((differentiableAt_const s).prodMk
      (mixedHybridMap_spatial_differentiable J f hr τ lam s θ hp hm hW))) using 1
    rfl
  have hvol := mixedHybridVolume_spatial_differentiable J f hr τ lam s θ hp hm hW
  have he : onsiteHybridPullback J f r τ lam F=
      fun t x => A t x*mixedHybridVolume J f r τ lam t x := by
    funext t x
    exact mul_comm _ _
  rw [he,lieStep_product_rule _ _ _ s θ hAs
    (mixedHybridVolume_parameter J f r τ lam s θ hs hW).differentiableAt hAx hvol
    (onsiteBranchField_spatial_differentiable J f hr τ lam s θ hp hm hg),
    onsite_volume_lie_zero J f hr τ lam s θ hs hp hm hplateau hW hg,
    ← mixedCoordinateTransport_eq_lie _ _ s θ hAx]
  rw [onsite_hybrid_transport_chain J f hr τ lam s θ hs
    (fun k => hp.differentiable (by simp) _) (fun k => hm.differentiable (by simp) _)
    hplateau hW hg F hF]
  simp only [mul_zero,zero_add,onsiteHybridPullback]
  ring

/-- Real cutoffs stay real and differentiated on the actual angular torus.
Every angular child has a regular branch coefficient; compact children vanish. -/
theorem onsite_weighted_pullback_step {n : ℕ}
    (J : Finset (Fin (n+1))) (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (θ : Fin (n+1) → ℝ) (hs : s≠0)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hplateau : ∀ i∈J,deriv f.p (θ i)=0 ∧ deriv f.m (θ i)=0)
    (hW : ∀ i∈J,0<(sourceW s (deformedPoint f r τ lam θ i)).im)
    (hg : ∀ i∈J,deformedPoint f r τ lam θ i-(deformedPoint f r τ lam θ i)⁻¹≠0)
    (w : (Fin (n+1) → ℝ) → ℝ) (hw : DifferentiableAt ℝ w θ)
    (F : ℂ → (Fin (n+1) → ℂ) → ℂ)
    (hF : DifferentiableAt ℂ (fun z : ℂ × (Fin (n+1) → ℂ) => F z.1 z.2)
      (s,mixedHybridMap J f r τ lam s θ)) :
    lieStep (onsiteBranchField J f r τ lam)
      (fun t x => (w x:ℂ)*onsiteHybridPullback J f r τ lam F t x) s θ =
      (w θ:ℂ)*onsiteHybridPullback J f r τ lam
        (fun t φ => deriv (fun z => F z φ) t) s θ -
      (∑ i∈J,mixedSourceA s (deformedPoint f r τ lam θ i)*
        (fderiv ℝ w θ (Pi.single i 1):ℂ))*onsiteHybridPullback J f r τ lam F s θ := by
  obtain ⟨hFs,hFx⟩ := onsiteHybridPullback_differentiable J f hr τ lam s θ hs hp hm hW F hF
  rw [lieStep_real_weight _ _ _ s θ hw hFs hFx
    (onsiteBranchField_spatial_differentiable J f hr τ lam s θ hp hm hg),
    onsiteHybridPullback_lie J f hr τ lam s θ hs hp hm hplateau hW hg F hF]
  simp [onsiteBranchField,ite_mul,Finset.sum_ite_mem]

end
end IsingBulk.HT.Lie
