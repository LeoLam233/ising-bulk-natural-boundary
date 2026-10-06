import IsingBulk.Tail.CompactRegularDensity
import IsingBulk.Tail.MixedDensityLieGerm

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Lie Set Filter
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false

theorem parameterSmooth_iterate_mul_frozen {n : ℕ} {Ω : Set (ℂ × AngularSpace n)}
    (hΩ : IsOpen Ω) (V : ℂ → AngularSpace n → Fin (n+1) → ℂ)
    (K A : ℂ → AngularSpace n → ℂ)
    (hV : ∀ i, ParameterSmoothOn Ω (fun s x => V s x i))
    (hK : ParameterSmoothOn Ω K) (hA : ParameterSmoothOn Ω A)
    (hfreeze : ∀ p ∈ Ω, transport V K p.1 p.2=0) (k : ℕ) :
    ∀ p ∈ Ω, ((lieStep V)^[k] (fun s x => K s x*A s x)) p.1 p.2=
      K p.1 p.2*((lieStep V)^[k] A) p.1 p.2 := by
  induction k with
  | zero => intro p hp; rfl
  | succ k ih =>
    intro p hp
    have he : Function.uncurry ((lieStep V)^[k] (fun s x => K s x*A s x)) =ᶠ[𝓝 p]
        Function.uncurry (fun s x => K s x*((lieStep V)^[k] A) s x) := by
      filter_upwards [hΩ.mem_nhds hp] with q hq
      exact ih q hq
    have hAk := hA.iterate_lieStep hΩ V A hV k
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply',lieStep_congr_joint_germ V p.1 p.2 he]
    exact lieStep_mul_frozen V K _ p.1 p.2 (hK p hp).2 (hAk p hp).2
      (hK.angular_differentiableAt hp) (hAk.angular_differentiableAt hp)
      (fun i => (hV i).angular_differentiableAt hp) (hfreeze p hp)

/-- Every order of the actual selected-pair Lie density has the original
two simple poles factored out, with the coupled determinant and all source
normalizations retained in the regular density. -/
theorem compact_selected_density_all_order {n : ℕ}
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ lam : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam) (i j : Fin (n+1))
    (w : AngularSpace n → ℂ)
    (hw : ParameterSmoothOn (compactSelectedDomain f r τ lam i j) (fun _ x => w x))
    (k : ℕ) {s : ℂ} {θ : AngularSpace n} (h : (s,θ) ∈ compactSelectedDomain f r τ lam i j) :
    ((lieStep (currentSelectedPairField f r τ lam i j))^[k]
      (fun z x => w x*pulledDensity f r τ lam z x)) s θ=
      mixedSimpleKernel f r τ lam s θ*
        ((lieStep (currentSelectedPairField f r τ lam i j))^[k]
          (fun z x => w x*compactRegularDensity f r τ lam z x)) s θ := by
  let Ω := compactSelectedDomain f r τ lam i j
  have hΩ := compactSelectedDomain_isOpen (Nat.succ_pos n) f hf hr hr1 hτ hlam i j
  have hV := currentSelectedPairField_smooth (Nat.succ_pos n) f hf hr hr1 hτ hlam i j
  have hK : ParameterSmoothOn Ω (mixedSimpleKernel f r τ lam) :=
    fun p hp => (compactSource_kernel_smooth (Nat.succ_pos n) f hf hr hr1 hτ hlam) p hp.1
  have hA : ParameterSmoothOn Ω (fun z x => w x*compactRegularDensity f r τ lam z x) :=
    hw.mul (fun p hp => (compactRegularDensity_smooth (Nat.succ_pos n) f hf hr hr1 hτ hlam) p hp.1)
  have he : (fun z x => w x*pulledDensity f r τ lam z x)=
      (fun z x => mixedSimpleKernel f r τ lam z x*(w x*compactRegularDensity f r τ lam z x)) := by
    funext z x
    rw [compact_pulledDensity_factorization]
    ring
  rw [he]
  exact parameterSmooth_iterate_mul_frozen hΩ _ _ _ hV hK hA
    (fun p hp => currentSelectedPairField_kernel_frozen f hf hr hr1 hτ hlam i j hp.1.1 p.2 hp.2) k (s,θ) h

theorem compact_selected_density_stages_smooth {n : ℕ}
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ lam : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam) (i j : Fin (n+1))
    (w : AngularSpace n → ℂ)
    (hw : ParameterSmoothOn (compactSelectedDomain f r τ lam i j) (fun _ x => w x)) (k : ℕ) :
    ParameterSmoothOn (compactSelectedDomain f r τ lam i j)
      ((lieStep (currentSelectedPairField f r τ lam i j))^[k]
        (fun z x => w x*pulledDensity f r τ lam z x)) :=
  (hw.mul (fun p hp => (compactSource_density_smooth (Nat.succ_pos n) f hf hr hr1 hτ hlam) p hp.1)).iterate_lieStep
    (compactSelectedDomain_isOpen (Nat.succ_pos n) f hf hr hr1 hτ hlam i j) _ _
    (currentSelectedPairField_smooth (Nat.succ_pos n) f hf hr hr1 hτ hlam i j) k

end
end IsingBulk.Tail
