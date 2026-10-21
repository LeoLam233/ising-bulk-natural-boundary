import IsingBulk.Tail.CompactSelectedLieDensity
import IsingBulk.HT.Tail.SignedCompactKernelTransport

namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail IsingBulk.Lie IsingBulk.HT.Contour Set Filter MeasureTheory Function
open scoped Topology ContDiff BigOperators
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem signed_compact_selected_density_all_order (σ : ℂ) (hσ : ‖σ‖ = 1) {n : ℕ}
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ lam : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam) (i j : Fin (n+1))
    (w : AngularSpace n → ℂ)
    (hw : ParameterSmoothOn (compactSelectedDomain f r τ lam i j) (fun _ x => w x))
    (k : ℕ) {s : ℂ} {θ : AngularSpace n} (h : (s,θ) ∈ compactSelectedDomain f r τ lam i j) :
    ((lieStep (currentSelectedPairField f r τ lam i j))^[k]
      (fun z x => w x*signedPulledDensity σ f r τ lam z x)) s θ=
      signedMixedSimpleKernel σ f r τ lam s θ*
        ((lieStep (currentSelectedPairField f r τ lam i j))^[k]
          (fun z x => w x*compactRegularDensity f r τ lam z x)) s θ := by
  let Ω := compactSelectedDomain f r τ lam i j
  have hΩ := compactSelectedDomain_isOpen (Nat.succ_pos n) f hf hr hr1 hτ hlam i j
  have hV := currentSelectedPairField_smooth (Nat.succ_pos n) f hf hr hr1 hτ hlam i j
  have hK : ParameterSmoothOn Ω (signedMixedSimpleKernel σ f r τ lam) :=
    fun p hp => (signed_compactSource_kernel_smooth σ hσ (Nat.succ_pos n) f hf hr hr1 hτ hlam) p hp.1
  have hA : ParameterSmoothOn Ω (fun z x => w x*compactRegularDensity f r τ lam z x) :=
    hw.mul (fun p hp => (compactRegularDensity_smooth (Nat.succ_pos n) f hf hr hr1 hτ hlam) p hp.1)
  have he : (fun z x => w x*signedPulledDensity σ f r τ lam z x)=
      (fun z x => signedMixedSimpleKernel σ f r τ lam z x*(w x*compactRegularDensity f r τ lam z x)) := by
    funext z x
    rw [signed_compact_pulledDensity_factorization]
    ring
  rw [he]
  exact parameterSmooth_iterate_mul_frozen hΩ _ _ _ hV hK hA
    (fun p hp => signed_currentSelectedPairField_kernel_frozen σ hσ f hf hr hr1 hτ hlam i j hp.1.1 p.2 hp.2) k (s,θ) h

theorem signed_compact_selected_density_stages_smooth (σ : ℂ) (hσ : ‖σ‖ = 1) {n : ℕ}
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ lam : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam) (i j : Fin (n+1))
    (w : AngularSpace n → ℂ)
    (hw : ParameterSmoothOn (compactSelectedDomain f r τ lam i j) (fun _ x => w x)) (k : ℕ) :
    ParameterSmoothOn (compactSelectedDomain f r τ lam i j)
      ((lieStep (currentSelectedPairField f r τ lam i j))^[k]
        (fun z x => w x*signedPulledDensity σ f r τ lam z x)) :=
  (hw.mul (fun p hp => (signed_compactSource_density_smooth σ hσ (Nat.succ_pos n) f hf hr hr1 hτ hlam) p hp.1)).iterate_lieStep
    (compactSelectedDomain_isOpen (Nat.succ_pos n) f hf hr hr1 hτ hlam i j) _ _
    (currentSelectedPairField_smooth (Nat.succ_pos n) f hf hr hr1 hτ hlam i j) k

end
end IsingBulk.HT.Tail
