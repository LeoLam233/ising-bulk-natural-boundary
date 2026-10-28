import IsingBulk.HT22.Tail.MixedRecursion
import IsingBulk.Preferred22.FrameAlgebra

/-! Actual fixed-v commuting-frame differential-polynomial calculus.
Only common finite list/product rules are imported; the parameter frame,
collective field, ordinary bordered kernel, and their jets are HT22 objects. -/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

def frameStep {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ) (a : Option (Fin N))
    (F : ℂ → (Fin N → ℝ) → ℂ) : ℂ → (Fin N → ℝ) → ℂ :=
  match a with
  | none => parameterFrame τ p m F
  | some i => coordinateFrame τ p m i F

def frameJet {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (F : ℂ → (Fin N → ℝ) → ℂ) : List (Option (Fin N)) → ℂ → (Fin N → ℝ) → ℂ
  | [] => F
  | a::xs => frameStep τ p m a (frameJet τ p m F xs)

theorem frameJet_cons {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (F : ℂ → (Fin N → ℝ) → ℂ) (a : Option (Fin N)) (xs : List (Option (Fin N))) :
    frameJet τ p m F (a::xs)=frameStep τ p m a (frameJet τ p m F xs) := by
  cases a <;> rfl

theorem frameStep_mixed {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hR : ∀ z∈Ω, sourceCovariance z.1 (sourceCoordinate τ p m z.1 z.2)≠0)
    (a : Option (Fin N)) (F : ℂ → (Fin N → ℝ) → ℂ)
    (hF : PreferredMixedSmoothOn (fun z => F z.1 z.2) Ω) :
    PreferredMixedSmoothOn (fun z => frameStep τ p m a F z.1 z.2) Ω := by
  obtain ⟨hMi,hv,hu,_hB⟩ := source_generator_factors_mixed τ δ p m hp hm Ω hpoint hR
  cases a with
  | none =>
    exact (hF.parameter hΩ).add (PreferredMixedSmoothOn.sum (fun i =>
      (PreferredMixedSmoothOn.sum (fun j => (hMi i j).mul (hu j))).mul (hF.coordinate hΩ i)))
  | some a =>
    exact PreferredMixedSmoothOn.sum (fun i => ((hMi i a).mul (hv a)).mul (hF.coordinate hΩ i))

theorem frameJet_mixed {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hR : ∀ z∈Ω, sourceCovariance z.1 (sourceCoordinate τ p m z.1 z.2)≠0)
    (F : ℂ → (Fin N → ℝ) → ℂ)
    (hF : PreferredMixedSmoothOn (fun z => F z.1 z.2) Ω)
    (xs : List (Option (Fin N))) :
    PreferredMixedSmoothOn (fun z => frameJet τ p m F xs z.1 z.2) Ω := by
  induction xs with
  | nil => exact hF
  | cons a xs ih =>
    rw [frameJet_cons]
    exact frameStep_mixed τ δ p m hp hm Ω hΩ hpoint hR a _ ih

theorem frameStep_mul {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ) (a : Option (Fin N))
    (F G : ℂ → (Fin N → ℝ) → ℂ) (s : ℂ) (θ : Fin N → ℝ)
    (hFs : DifferentiableAt ℂ (fun t => F t θ) s)
    (hGs : DifferentiableAt ℂ (fun t => G t θ) s)
    (hFθ : ∀ i, DifferentiableAt ℝ (fun x => F s (Function.update θ i x)) (θ i))
    (hGθ : ∀ i, DifferentiableAt ℝ (fun x => G s (Function.update θ i x)) (θ i)) :
    frameStep τ p m a (fun t x => F t x*G t x) s θ=
      frameStep τ p m a F s θ*G s θ+F s θ*frameStep τ p m a G s θ := by
  have hs := (hFs.hasDerivAt.fun_mul hGs.hasDerivAt).deriv
  have hx (i : Fin N) := ((hFθ i).hasDerivAt.fun_mul (hGθ i).hasDerivAt).deriv
  simp only [Function.update_eq_self] at hx
  cases a with
  | none =>
    simp only [frameStep,parameterFrame]
    rw [hs]
    simp_rw [hx]
    rw [sum_material_product]
    ring
  | some a =>
    simp only [frameStep,coordinateFrame]
    simp_rw [hx]
    exact sum_material_product _ _ _ _ _

theorem frameStep_add {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ) (a : Option (Fin N))
    (F G : ℂ → (Fin N → ℝ) → ℂ) (s : ℂ) (θ : Fin N → ℝ)
    (hFs : DifferentiableAt ℂ (fun t => F t θ) s)
    (hGs : DifferentiableAt ℂ (fun t => G t θ) s)
    (hFθ : ∀ i, DifferentiableAt ℝ (fun x => F s (Function.update θ i x)) (θ i))
    (hGθ : ∀ i, DifferentiableAt ℝ (fun x => G s (Function.update θ i x)) (θ i)) :
    frameStep τ p m a (fun t x => F t x+G t x) s θ=
      frameStep τ p m a F s θ+frameStep τ p m a G s θ := by
  have hs := (hFs.hasDerivAt.fun_add hGs.hasDerivAt).deriv
  have hx (i : Fin N) := ((hFθ i).hasDerivAt.fun_add (hGθ i).hasDerivAt).deriv
  cases a with
  | none =>
    simp only [frameStep,parameterFrame]
    rw [hs]
    simp_rw [hx]
    simp only [mul_add,Finset.sum_add_distrib]
    ring
  | some a =>
    simp only [frameStep,coordinateFrame]
    simp_rw [hx]
    simp only [mul_add,Finset.sum_add_distrib]

theorem frameStep_zero {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ) (a : Option (Fin N)) :
    frameStep τ p m a (fun _ _ => (0:ℂ))=(fun _ _ => 0) := by
  funext s θ
  cases a <;> simp [frameStep,parameterFrame,coordinateFrame]

theorem frameStep_list_sum {N : ℕ} {ι : Type*} (τ : ℝ) (p m : ℝ → ℝ)
    (a : Option (Fin N)) (F : ι → ℂ → (Fin N → ℝ) → ℂ) (L : List ι)
    (Ω : Set (ℂ × (Fin N → ℝ)))
    (hF : ∀ i∈L, PreferredMixedSmoothOn (fun z => F i z.1 z.2) Ω)
    (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    frameStep τ p m a (fun t x => (L.map (fun i => F i t x)).sum) s θ=
      (L.map (fun i => frameStep τ p m a (F i) s θ)).sum := by
  induction L with
  | nil => simp [frameStep_zero]
  | cons i L ih =>
    have hi := hF i (List.mem_cons_self ..)
    have ht := PreferredMixedSmoothOn.list_sum (fun i z => F i z.1 z.2) L Ω
      (fun j hj => hF j (List.mem_cons_of_mem _ hj))
    simp only [List.map_cons,List.sum_cons]
    rw [frameStep_add τ p m a (F i) _ s θ (hi (s,θ) hz).2 (ht (s,θ) hz).2
      (preferredMixed_coordinate_differentiable _ s θ (hi (s,θ) hz).1)
      (preferredMixed_coordinate_differentiable _ s θ (ht (s,θ) hz).1)]
    rw [ih (fun j hj => hF j (List.mem_cons_of_mem _ hj))]

theorem regularTransportStep_add {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (F G : ℂ → (Fin N → ℝ) → ℂ) (s : ℂ) (θ : Fin N → ℝ)
    (hFs : DifferentiableAt ℂ (fun t => F t θ) s)
    (hGs : DifferentiableAt ℂ (fun t => G t θ) s)
    (hFθ : ∀ i, DifferentiableAt ℝ (fun x => F s (Function.update θ i x)) (θ i))
    (hGθ : ∀ i, DifferentiableAt ℝ (fun x => G s (Function.update θ i x)) (θ i)) :
    regularTransportStep τ p m (fun t x => F t x+G t x) s θ=
      regularTransportStep τ p m F s θ+regularTransportStep τ p m G s θ := by
  have hs := (hFs.hasDerivAt.fun_add hGs.hasDerivAt).deriv
  have hx (i : Fin N) := ((hFθ i).hasDerivAt.fun_add (hGθ i).hasDerivAt).deriv
  simp only [regularTransportStep_eq]
  rw [hs]
  simp_rw [hx]
  simp only [mul_add,Finset.sum_add_distrib]
  ring

theorem regularTransportStep_zero {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ) :
    regularTransportStep (N:=N) τ p m (fun _ _ => (0:ℂ))=(fun _ _ => 0) := by
  funext s θ
  simp [regularTransportStep_eq]

theorem regularTransportStep_list_sum {N : ℕ} {ι : Type*} (τ : ℝ) (p m : ℝ → ℝ)
    (F : ι → ℂ → (Fin N → ℝ) → ℂ) (L : List ι) (Ω : Set (ℂ × (Fin N → ℝ)))
    (hF : ∀ i∈L, PreferredMixedSmoothOn (fun z => F i z.1 z.2) Ω)
    (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    regularTransportStep τ p m (fun t x => (L.map (fun i => F i t x)).sum) s θ=
      (L.map (fun i => regularTransportStep τ p m (F i) s θ)).sum := by
  induction L with
  | nil => simp [regularTransportStep_zero]
  | cons i L ih =>
    have hi := hF i (List.mem_cons_self ..)
    have ht := PreferredMixedSmoothOn.list_sum (fun i z => F i z.1 z.2) L Ω
      (fun j hj => hF j (List.mem_cons_of_mem _ hj))
    simp only [List.map_cons,List.sum_cons]
    rw [regularTransportStep_add τ p m (F i) _ s θ (hi (s,θ) hz).2 (ht (s,θ) hz).2
      (preferredMixed_coordinate_differentiable _ s θ (hi (s,θ) hz).1)
      (preferredMixed_coordinate_differentiable _ s θ (ht (s,θ) hz).1)]
    rw [ih (fun j hj => hF j (List.mem_cons_of_mem _ hj))]

theorem ordinaryMaterialEntry_eq_frames {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (s : ℂ) (θ : Fin N → ℝ) (ij : Fin N × Fin N)
    (hs : DifferentiableAt ℂ (fun t => sourceOrdinaryKernel τ p m t θ) s)
    (hθ : ∀ i, DifferentiableAt ℝ
      (fun x => sourceOrdinaryKernel τ p m s (Function.update θ i x)) (θ i)) :
    ordinaryMaterialEntry τ p m s θ ij=
      frameStep τ p m none (fun t x => sourceOrdinaryKernel τ p m t x ij.1 ij.2) s θ+
        ∑ a, residualField s (sourceCoordinate τ p m s θ) a *
          frameStep τ p m (some a)
            (fun t x => sourceOrdinaryKernel τ p m t x ij.1 ij.2) s θ := by
  have hsd := hasDerivAt_pi.mp (hasDerivAt_pi.mp hs.hasDerivAt ij.1) ij.2
  have hθd (a : Fin N) := hasDerivAt_pi.mp (hasDerivAt_pi.mp (hθ a).hasDerivAt ij.1) ij.2
  have hh := regularTransportStep_eq τ p m
    (fun t x => sourceOrdinaryKernel τ p m t x ij.1 ij.2) s θ
  unfold regularTransportStep at hh
  have he := add_right_cancel hh
  unfold ordinaryMaterialEntry
  rw [←hsd.deriv]
  simp_rw [←(hθd _).deriv]
  exact he.symm

end
end IsingBulk.HT22.Tail
