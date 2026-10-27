import IsingBulk.Preferred22.SourceMixedFactors

/-! Real-cutoff frame calculus for the scalar differential-polynomial
expansion. The literal source frames are derivations on the actual mixed
smooth functions; no complex continuation of a real cutoff is used. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

def preferredFrameStep {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ) (a : Option (Fin N))
    (F : ℂ → (Fin N → ℝ) → ℂ) : ℂ → (Fin N → ℝ) → ℂ :=
  match a with
  | none => preferredParameterFrame τ p m F
  | some i => preferredCoordinateFrame τ p m i F

theorem preferredFrameJet_cons {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (F : ℂ → (Fin N → ℝ) → ℂ) (a : Option (Fin N)) (xs : List (Option (Fin N))) :
    preferredFrameJet τ p m F (a::xs)=preferredFrameStep τ p m a (preferredFrameJet τ p m F xs) := by
  cases a <;> rfl

theorem PreferredMixedSmoothOn.list_sum {N : ℕ} {ι : Type*}
    (F : ι → ℂ × (Fin N → ℝ) → ℂ) (L : List ι) (Ω : Set (ℂ × (Fin N → ℝ)))
    (hF : ∀ i∈L, PreferredMixedSmoothOn (F i) Ω) :
    PreferredMixedSmoothOn (fun z => (L.map (fun i => F i z)).sum) Ω := by
  induction L with
  | nil => exact PreferredMixedSmoothOn.const Ω 0
  | cons i L ih =>
    exact (hF i (List.mem_cons_self ..)).add
      (ih (fun j hj => hF j (List.mem_cons_of_mem _ hj)))

theorem PreferredMixedSmoothOn.list_prod {N : ℕ} {ι : Type*}
    (F : ι → ℂ × (Fin N → ℝ) → ℂ) (L : List ι) (Ω : Set (ℂ × (Fin N → ℝ)))
    (hF : ∀ i∈L, PreferredMixedSmoothOn (F i) Ω) :
    PreferredMixedSmoothOn (fun z => (L.map (fun i => F i z)).prod) Ω := by
  induction L with
  | nil => exact PreferredMixedSmoothOn.const Ω 1
  | cons i L ih =>
    exact (hF i (List.mem_cons_self ..)).mul
      (ih (fun j hj => hF j (List.mem_cons_of_mem _ hj)))

theorem preferredFrameStep_mixed {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (a : Option (Fin N)) (F : ℂ → (Fin N → ℝ) → ℂ)
    (hF : PreferredMixedSmoothOn (fun z => F z.1 z.2) Ω) :
    PreferredMixedSmoothOn (fun z => preferredFrameStep τ p m a F z.1 z.2) Ω := by
  have hMi (i j : Fin N) : PreferredMixedSmoothOn
      (fun z => (preferredContourMatrix τ p m z.2)⁻¹ i j) Ω := by
    intro z hz
    have hh := preferredContourMatrix_inverse_contDiffAt τ p m hp hm z.2 (hpoint z hz).matrix
    exact ⟨(contDiffAt_pi.mp (contDiffAt_pi.mp hh i) j).comp z contDiffAt_snd,
      differentiableAt_const (𝕜:=ℂ) (x:=z.1) ((preferredContourMatrix τ p m z.2)⁻¹ i j)⟩
  have hv (j : Fin N) : PreferredMixedSmoothOn
      (fun z => preferredSourceUQ z.1 (preferredSourceCoordinate τ p m z.1 z.2 j)) Ω := by
    intro z hz
    have h := hpoint z hz
    exact ⟨contDiffAt_pi.mp (preferredSourceInverseDerivatives_contDiffAt τ p m hp hm z.1 z.2
      h.trace_im h.upper h.inverse_analytic).1 j,
      (analyticAt_pi_iff.mp (preferredSourceInverseDerivatives_parameter_analyticAt τ p m z.1 z.2
        h.trace_im h.upper h.inverse_analytic).1 j).differentiableAt⟩
  have hu (j : Fin N) : PreferredMixedSmoothOn
      (fun z => preferredSourceUDot z.1 (preferredSourceCoordinate τ p m z.1 z.2 j)) Ω := by
    intro z hz
    have h := hpoint z hz
    exact ⟨contDiffAt_pi.mp (preferredSourceInverseDerivatives_contDiffAt τ p m hp hm z.1 z.2
      h.trace_im h.upper h.inverse_analytic).2 j,
      (analyticAt_pi_iff.mp (preferredSourceInverseDerivatives_parameter_analyticAt τ p m z.1 z.2
        h.trace_im h.upper h.inverse_analytic).2 j).differentiableAt⟩
  cases a with
  | none =>
    exact (hF.parameter hΩ).add (PreferredMixedSmoothOn.sum (fun i =>
      (PreferredMixedSmoothOn.sum (fun j => (hMi i j).mul (hu j))).mul (hF.coordinate hΩ i)))
  | some a =>
    exact PreferredMixedSmoothOn.sum (fun i => ((hMi i a).mul (hv a)).mul (hF.coordinate hΩ i))

theorem preferredFrameJet_mixed {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (F : ℂ → (Fin N → ℝ) → ℂ)
    (hF : PreferredMixedSmoothOn (fun z => F z.1 z.2) Ω)
    (xs : List (Option (Fin N))) :
    PreferredMixedSmoothOn (fun z => preferredFrameJet τ p m F xs z.1 z.2) Ω := by
  induction xs with
  | nil => exact hF
  | cons a xs ih =>
    rw [preferredFrameJet_cons]
    exact preferredFrameStep_mixed τ δ p m hp hm Ω hΩ hpoint a _ ih

theorem preferredMixed_coordinate_differentiable {N : ℕ}
    (F : ℂ → (Fin N → ℝ) → ℂ) (s : ℂ) (θ : Fin N → ℝ)
    (hF : ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) => F z.1 z.2) (s,θ)) (i : Fin N) :
    DifferentiableAt ℝ (fun x => F s (Function.update θ i x)) (θ i) := by
  have hh := hF.differentiableAt (by simp)
  have hg := (hasDerivAt_const (θ i) s).prodMk (hasDerivAt_update θ i (θ i))
  exact (hh.hasFDerivAt.comp_hasDerivAt_of_eq (θ i) hg
    (by simp only [Function.update_eq_self])).differentiableAt

theorem preferredFrameStep_mul {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ) (a : Option (Fin N))
    (F G : ℂ → (Fin N → ℝ) → ℂ) (s : ℂ) (θ : Fin N → ℝ)
    (hFs : DifferentiableAt ℂ (fun t => F t θ) s)
    (hGs : DifferentiableAt ℂ (fun t => G t θ) s)
    (hFθ : ∀ i, DifferentiableAt ℝ (fun x => F s (Function.update θ i x)) (θ i))
    (hGθ : ∀ i, DifferentiableAt ℝ (fun x => G s (Function.update θ i x)) (θ i)) :
    preferredFrameStep τ p m a (fun t x => F t x*G t x) s θ=
      preferredFrameStep τ p m a F s θ*G s θ+F s θ*preferredFrameStep τ p m a G s θ := by
  have hs := (hFs.hasDerivAt.fun_mul hGs.hasDerivAt).deriv
  have hx (i : Fin N) := ((hFθ i).hasDerivAt.fun_mul (hGθ i).hasDerivAt).deriv
  simp only [Function.update_eq_self] at hx
  cases a with
  | none =>
    simp only [preferredFrameStep,preferredParameterFrame]
    rw [hs]
    simp_rw [hx]
    rw [sum_material_product]
    ring
  | some a =>
    simp only [preferredFrameStep,preferredCoordinateFrame]
    simp_rw [hx]
    exact sum_material_product _ _ _ _ _

theorem preferredFrameStep_add {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ) (a : Option (Fin N))
    (F G : ℂ → (Fin N → ℝ) → ℂ) (s : ℂ) (θ : Fin N → ℝ)
    (hFs : DifferentiableAt ℂ (fun t => F t θ) s)
    (hGs : DifferentiableAt ℂ (fun t => G t θ) s)
    (hFθ : ∀ i, DifferentiableAt ℝ (fun x => F s (Function.update θ i x)) (θ i))
    (hGθ : ∀ i, DifferentiableAt ℝ (fun x => G s (Function.update θ i x)) (θ i)) :
    preferredFrameStep τ p m a (fun t x => F t x+G t x) s θ=
      preferredFrameStep τ p m a F s θ+preferredFrameStep τ p m a G s θ := by
  have hs := (hFs.hasDerivAt.fun_add hGs.hasDerivAt).deriv
  have hx (i : Fin N) := ((hFθ i).hasDerivAt.fun_add (hGθ i).hasDerivAt).deriv
  cases a with
  | none =>
    simp only [preferredFrameStep,preferredParameterFrame]
    rw [hs]
    simp_rw [hx]
    simp only [mul_add,Finset.sum_add_distrib]
    ring
  | some a =>
    simp only [preferredFrameStep,preferredCoordinateFrame]
    simp_rw [hx]
    simp only [mul_add,Finset.sum_add_distrib]

theorem preferredFrameStep_zero {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ) (a : Option (Fin N)) :
    preferredFrameStep τ p m a (fun _ _ => (0:ℂ))=(fun _ _ => 0) := by
  funext s θ
  cases a <;> simp [preferredFrameStep,preferredParameterFrame,preferredCoordinateFrame]

theorem preferredFrameStep_list_sum {N : ℕ} {ι : Type*} (τ : ℝ) (p m : ℝ → ℝ)
    (a : Option (Fin N)) (F : ι → ℂ → (Fin N → ℝ) → ℂ) (L : List ι)
    (Ω : Set (ℂ × (Fin N → ℝ)))
    (hF : ∀ i∈L, PreferredMixedSmoothOn (fun z => F i z.1 z.2) Ω)
    (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    preferredFrameStep τ p m a (fun t x => (L.map (fun i => F i t x)).sum) s θ=
      (L.map (fun i => preferredFrameStep τ p m a (F i) s θ)).sum := by
  induction L with
  | nil => simp [preferredFrameStep_zero]
  | cons i L ih =>
    have hi := hF i (List.mem_cons_self ..)
    have ht := PreferredMixedSmoothOn.list_sum (fun i z => F i z.1 z.2) L Ω
      (fun j hj => hF j (List.mem_cons_of_mem _ hj))
    simp only [List.map_cons,List.sum_cons]
    rw [preferredFrameStep_add τ p m a (F i) _ s θ (hi (s,θ) hz).2 (ht (s,θ) hz).2
      (preferredMixed_coordinate_differentiable _ s θ (hi (s,θ) hz).1)
      (preferredMixed_coordinate_differentiable _ s θ (ht (s,θ) hz).1)]
    rw [ih (fun j hj => hF j (List.mem_cons_of_mem _ hj))]

theorem preferredRegularTransportStep_add {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (F G : ℂ → (Fin N → ℝ) → ℂ) (s : ℂ) (θ : Fin N → ℝ)
    (hFs : DifferentiableAt ℂ (fun t => F t θ) s)
    (hGs : DifferentiableAt ℂ (fun t => G t θ) s)
    (hFθ : ∀ i, DifferentiableAt ℝ (fun x => F s (Function.update θ i x)) (θ i))
    (hGθ : ∀ i, DifferentiableAt ℝ (fun x => G s (Function.update θ i x)) (θ i)) :
    preferredRegularTransportStep τ p m (fun t x => F t x+G t x) s θ=
      preferredRegularTransportStep τ p m F s θ+preferredRegularTransportStep τ p m G s θ := by
  have hs := (hFs.hasDerivAt.fun_add hGs.hasDerivAt).deriv
  have hx (i : Fin N) := ((hFθ i).hasDerivAt.fun_add (hGθ i).hasDerivAt).deriv
  simp only [preferredRegularTransportStep_eq]
  rw [hs]
  simp_rw [hx]
  simp only [mul_add,Finset.sum_add_distrib]
  ring

theorem preferredRegularTransportStep_zero {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ) :
    preferredRegularTransportStep (N:=N) τ p m (fun _ _ => (0:ℂ))=(fun _ _ => 0) := by
  funext s θ
  simp [preferredRegularTransportStep_eq]

theorem preferredRegularTransportStep_list_sum {N : ℕ} {ι : Type*} (τ : ℝ) (p m : ℝ → ℝ)
    (F : ι → ℂ → (Fin N → ℝ) → ℂ) (L : List ι) (Ω : Set (ℂ × (Fin N → ℝ)))
    (hF : ∀ i∈L, PreferredMixedSmoothOn (fun z => F i z.1 z.2) Ω)
    (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    preferredRegularTransportStep τ p m (fun t x => (L.map (fun i => F i t x)).sum) s θ=
      (L.map (fun i => preferredRegularTransportStep τ p m (F i) s θ)).sum := by
  induction L with
  | nil => simp [preferredRegularTransportStep_zero]
  | cons i L ih =>
    have hi := hF i (List.mem_cons_self ..)
    have ht := PreferredMixedSmoothOn.list_sum (fun i z => F i z.1 z.2) L Ω
      (fun j hj => hF j (List.mem_cons_of_mem _ hj))
    simp only [List.map_cons,List.sum_cons]
    rw [preferredRegularTransportStep_add τ p m (F i) _ s θ (hi (s,θ) hz).2 (ht (s,θ) hz).2
      (preferredMixed_coordinate_differentiable _ s θ (hi (s,θ) hz).1)
      (preferredMixed_coordinate_differentiable _ s θ (ht (s,θ) hz).1)]
    rw [ih (fun j hj => hF j (List.mem_cons_of_mem _ hj))]

theorem preferredKernelMaterialEntry_eq_frames {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (s : ℂ) (θ : Fin N → ℝ) (ij : Fin N × Fin N)
    (hs : DifferentiableAt ℂ (fun t => preferredSourceRegularKernel τ p m t θ) s)
    (hθ : ∀ i, DifferentiableAt ℝ
      (fun x => preferredSourceRegularKernel τ p m s (Function.update θ i x)) (θ i)) :
    preferredKernelMaterialEntry τ p m s θ ij=
      preferredFrameStep τ p m none (fun t x => preferredSourceRegularKernel τ p m t x ij.1 ij.2) s θ+
        ∑ a, preferredResidualCollective s (preferredSourceCoordinate τ p m s θ) a *
          preferredFrameStep τ p m (some a)
            (fun t x => preferredSourceRegularKernel τ p m t x ij.1 ij.2) s θ := by
  have hsd := hasDerivAt_pi.mp (hasDerivAt_pi.mp hs.hasDerivAt ij.1) ij.2
  have hθd (a : Fin N) := hasDerivAt_pi.mp (hasDerivAt_pi.mp (hθ a).hasDerivAt ij.1) ij.2
  have hh := preferredRegularTransportStep_eq τ p m
    (fun t x => preferredSourceRegularKernel τ p m t x ij.1 ij.2) s θ
  unfold preferredRegularTransportStep at hh
  have he := add_right_cancel hh
  unfold preferredKernelMaterialEntry
  rw [←hsd.deriv]
  simp_rw [←(hθd _).deriv]
  exact he.symm

end
end IsingBulk.Preferred22
