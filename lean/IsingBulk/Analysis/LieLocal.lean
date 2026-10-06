import IsingBulk.Analysis.LieTransport

/-! Locality of the actual differential operator. No derivative at a puncture
or kernel pole occurs in these theorems. -/
namespace IsingBulk.Lie
noncomputable section
open Set Filter
open scoped Topology

theorem lieStep_congr_on {n : ℕ}
    (V : ℂ → AngularSpace n → Fin (n+1) → ℂ)
    {A B : ℂ → AngularSpace n → ℂ} {U : Set ℂ} {R : Set (AngularSpace n)}
    (hU : IsOpen U) (hR : IsOpen R)
    (h : ∀ s ∈ U, EqOn (A s) (B s) R) {s : ℂ} (hs : s ∈ U)
    {x : AngularSpace n} (hx : x ∈ R) : lieStep V A s x = lieStep V B s x := by
  have hp : (fun t => A t x) =ᶠ[𝓝 s] (fun t => B t x) := by
    filter_upwards [hU.mem_nhds hs] with t ht using h t ht hx
  have hf : ∀ i, (fun y => V s y i * A s y) =ᶠ[𝓝 x]
      (fun y => V s y i * B s y) := by
    intro i
    filter_upwards [hR.mem_nhds hx] with y hy using congrArg (V s y i * ·) (h s hs hy)
  simp only [lieStep, divergence, hp.deriv_eq, (hf _).fderiv_eq]

theorem iterate_lieStep_congr_on {n : ℕ}
    (V : ℂ → AngularSpace n → Fin (n+1) → ℂ)
    {A B : ℂ → AngularSpace n → ℂ} {U : Set ℂ} {R : Set (AngularSpace n)}
    (hU : IsOpen U) (hR : IsOpen R)
    (h : ∀ s ∈ U, EqOn (A s) (B s) R) (j : ℕ) :
    ∀ s ∈ U, EqOn (((lieStep V)^[j] A) s) (((lieStep V)^[j] B) s) R := by
  induction j with
  | zero => exact h
  | succ j ih =>
    intro s hs x hx
    simpa only [Function.iterate_succ_apply'] using lieStep_congr_on V hU hR ih hs hx

theorem iterate_lieStep_mul_frozen_on {n : ℕ}
    (V : ℂ → AngularSpace n → Fin (n+1) → ℂ) (K A : ℂ → AngularSpace n → ℂ)
    (U : Set ℂ) (R : Set (AngularSpace n)) (hU : IsOpen U) (hR : IsOpen R)
    (hKs : ∀ s ∈ U, ∀ x ∈ R, DifferentiableAt ℂ (fun t => K t x) s)
    (hKx : ∀ s ∈ U, ∀ x ∈ R, DifferentiableAt ℝ (K s) x)
    (hV : ∀ s ∈ U, ∀ x ∈ R, ∀ i, DifferentiableAt ℝ (fun y => V s y i) x)
    (hfreeze : ∀ s ∈ U, ∀ x ∈ R, transport V K s x = 0) (j : ℕ)
    (hAs : ∀ k < j, ∀ s ∈ U, ∀ x ∈ R,
      DifferentiableAt ℂ (fun t => ((lieStep V)^[k] A) t x) s)
    (hAx : ∀ k < j, ∀ s ∈ U, ∀ x ∈ R,
      DifferentiableAt ℝ (((lieStep V)^[k] A) s) x) :
    ∀ s ∈ U, ∀ x ∈ R, (lieStep V)^[j] (fun t y => K t y * A t y) s x =
      K s x * ((lieStep V)^[j] A) s x := by
  induction j with
  | zero => intros; rfl
  | succ j ih =>
    have hp := ih (fun k hk => hAs k (by omega)) (fun k hk => hAx k (by omega))
    intro s hs x hx
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    rw [lieStep_congr_on V hU hR hp hs hx]
    exact lieStep_mul_frozen V K _ s x (hKs s hs x hx) (hAs j (by omega) s hs x hx)
      (hKx s hs x hx) (hAx j (by omega) s hs x hx) (hV s hs x hx) (hfreeze s hs x hx)

/-- Differentiability and freezing are required only on the regular locus. -/
structure FrozenKernel {n : ℕ} (U : Set ℂ) (R : Set (AngularSpace n))
    (V : ℂ → AngularSpace n → Fin (n+1) → ℂ) (Y Z : ℂ → AngularSpace n → ℂ) : Prop where
  Y_parameter : ∀ s ∈ U, ∀ x ∈ R, DifferentiableAt ℂ (fun t => Y t x) s
  Z_parameter : ∀ s ∈ U, ∀ x ∈ R, DifferentiableAt ℂ (fun t => Z t x) s
  Y_spatial : ∀ s ∈ U, ∀ x ∈ R, DifferentiableAt ℝ (Y s) x
  Z_spatial : ∀ s ∈ U, ∀ x ∈ R, DifferentiableAt ℝ (Z s) x
  Y_nonzero : ∀ s ∈ U, ∀ x ∈ R, 1 - Y s x ≠ 0
  Z_nonzero : ∀ s ∈ U, ∀ x ∈ R, 1 - Z s x ≠ 0
  Y_frozen : ∀ s ∈ U, ∀ x ∈ R, transport V Y s x = 0
  Z_frozen : ∀ s ∈ U, ∀ x ∈ R, transport V Z s x = 0

theorem FrozenKernel.parameter {n : ℕ} {U : Set ℂ} {R : Set (AngularSpace n)}
    {V : ℂ → AngularSpace n → Fin (n+1) → ℂ} {Y Z : ℂ → AngularSpace n → ℂ}
    (h : FrozenKernel U R V Y Z) {s : ℂ} (hs : s ∈ U) {x : AngularSpace n} (hx : x ∈ R) :
    DifferentiableAt ℂ (fun t => simpleKernel Y Z t x) s :=
  ((h.Y_parameter s hs x hx).const_sub 1 |>.inv (h.Y_nonzero s hs x hx)).mul
    ((h.Z_parameter s hs x hx).const_sub 1 |>.inv (h.Z_nonzero s hs x hx))

theorem FrozenKernel.spatial {n : ℕ} {U : Set ℂ} {R : Set (AngularSpace n)}
    {V : ℂ → AngularSpace n → Fin (n+1) → ℂ} {Y Z : ℂ → AngularSpace n → ℂ}
    (h : FrozenKernel U R V Y Z) {s : ℂ} (hs : s ∈ U) {x : AngularSpace n} (hx : x ∈ R) :
    DifferentiableAt ℝ (simpleKernel Y Z s) x :=
  ((h.Y_spatial s hs x hx).const_sub 1 |>.inv (h.Y_nonzero s hs x hx)).mul
    ((h.Z_spatial s hs x hx).const_sub 1 |>.inv (h.Z_nonzero s hs x hx))

theorem FrozenKernel.transport_zero {n : ℕ} {U : Set ℂ} {R : Set (AngularSpace n)}
    {V : ℂ → AngularSpace n → Fin (n+1) → ℂ} {Y Z : ℂ → AngularSpace n → ℂ}
    (h : FrozenKernel U R V Y Z) {s : ℂ} (hs : s ∈ U) {x : AngularSpace n} (hx : x ∈ R) :
    transport V (simpleKernel Y Z) s x = 0 :=
  simpleKernel_frozen V Y Z s x (h.Y_parameter s hs x hx) (h.Z_parameter s hs x hx)
    (h.Y_spatial s hs x hx) (h.Z_spatial s hs x hx) (h.Y_nonzero s hs x hx)
    (h.Z_nonzero s hs x hx) (h.Y_frozen s hs x hx) (h.Z_frozen s hs x hx)

theorem FrozenKernel.nonzero {n : ℕ} {U : Set ℂ} {R : Set (AngularSpace n)}
    {V : ℂ → AngularSpace n → Fin (n+1) → ℂ} {Y Z : ℂ → AngularSpace n → ℂ}
    (h : FrozenKernel U R V Y Z) {s : ℂ} (hs : s ∈ U) {x : AngularSpace n} (hx : x ∈ R) :
    simpleKernel Y Z s x ≠ 0 :=
  mul_ne_zero (inv_ne_zero (h.Y_nonzero s hs x hx)) (inv_ne_zero (h.Z_nonzero s hs x hx))

/-- Regularity of the full previous densities suffices. Apply the frozen
inverse kernel to those densities, so no independent regularity of generated
numerator stages needs to be assumed. -/
theorem iterate_lieStep_factor_from_full {n : ℕ}
    (V : ℂ → AngularSpace n → Fin (n+1) → ℂ) (K A B : ℂ → AngularSpace n → ℂ)
    (U : Set ℂ) (R : Set (AngularSpace n)) (hU : IsOpen U) (hR : IsOpen R)
    (hKs : ∀ s ∈ U, ∀ x ∈ R, DifferentiableAt ℂ (fun t => K t x) s)
    (hKx : ∀ s ∈ U, ∀ x ∈ R, DifferentiableAt ℝ (K s) x)
    (hK0 : ∀ s ∈ U, ∀ x ∈ R, K s x ≠ 0)
    (hV : ∀ s ∈ U, ∀ x ∈ R, ∀ i, DifferentiableAt ℝ (fun y => V s y i) x)
    (hfreeze : ∀ s ∈ U, ∀ x ∈ R, transport V K s x = 0)
    (hfactor : ∀ s ∈ U, ∀ x ∈ R, A s x = K s x * B s x) (j : ℕ)
    (hAs : ∀ k < j, ∀ s ∈ U, ∀ x ∈ R,
      DifferentiableAt ℂ (fun t => ((lieStep V)^[k] A) t x) s)
    (hAx : ∀ k < j, ∀ s ∈ U, ∀ x ∈ R,
      DifferentiableAt ℝ (((lieStep V)^[k] A) s) x) :
    ∀ s ∈ U, ∀ x ∈ R, ((lieStep V)^[j] A) s x = K s x * ((lieStep V)^[j] B) s x := by
  have hB : ∀ s ∈ U, EqOn (B s) (fun x => (K s x)⁻¹ * A s x) R := by
    intro s hs x hx
    dsimp only
    rw [hfactor s hs x hx, inv_mul_cancel_left₀ (hK0 s hs x hx)]
  have hInv : ∀ s ∈ U, ∀ x ∈ R, transport V (fun t y => (K t y)⁻¹) s x = 0 := by
    intro s hs x hx
    rw [transport_inv V K s x (hKs s hs x hx) (hKx s hs x hx) (hK0 s hs x hx),
      hfreeze s hs x hx, mul_zero]
  have hi := iterate_lieStep_mul_frozen_on V (fun t y => (K t y)⁻¹) A U R hU hR
    (fun s hs x hx => (hKs s hs x hx).inv (hK0 s hs x hx))
    (fun s hs x hx => (hKx s hs x hx).inv (hK0 s hs x hx)) hV hInv j hAs hAx
  intro s hs x hx
  rw [iterate_lieStep_congr_on V hU hR hB j s hs hx, hi s hs x hx,
    mul_inv_cancel_left₀ (hK0 s hs x hx)]

end
end IsingBulk.Lie
