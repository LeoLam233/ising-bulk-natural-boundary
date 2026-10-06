import IsingBulk.Tail.ParameterSmoothLie
import IsingBulk.Tail.SelectorSmoothDensity

namespace IsingBulk.Tail
noncomputable section
open Set
open scoped Topology ContDiff BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem ParameterSmoothOn.const (Ω : Set (ℂ × E)) (c : ℂ) :
    ParameterSmoothOn Ω (fun _ _ => c) := fun _ _ => ⟨contDiffAt_const,differentiableAt_const c⟩

theorem ParameterSmoothOn.parameter (Ω : Set (ℂ × E)) :
    ParameterSmoothOn Ω (fun s _ => s) := fun _ _ => ⟨contDiffAt_fst,differentiableAt_id⟩

theorem ParameterSmoothOn.angular (Ω : Set (ℂ × E)) (f : E → ℂ) (hf : ContDiff ℝ ∞ f) :
    ParameterSmoothOn Ω (fun _ y => f y) := by
  intro p _
  exact ⟨hf.contDiffAt.comp p contDiffAt_snd,differentiableAt_const _⟩

theorem ParameterSmoothOn.add {Ω : Set (ℂ × E)} {F G : ℂ → E → ℂ}
    (hF : ParameterSmoothOn Ω F) (hG : ParameterSmoothOn Ω G) :
    ParameterSmoothOn Ω (fun s y => F s y+G s y) := fun p hp =>
  ⟨(hF p hp).1.add (hG p hp).1,(hF p hp).2.add (hG p hp).2⟩

theorem ParameterSmoothOn.inv {Ω : Set (ℂ × E)} {F : ℂ → E → ℂ}
    (hF : ParameterSmoothOn Ω F) (hne : ∀ p∈Ω,F p.1 p.2≠0) :
    ParameterSmoothOn Ω (fun s y => (F s y)⁻¹) := fun p hp =>
  ⟨(hF p hp).1.inv (hne p hp),(hF p hp).2.inv (hne p hp)⟩

theorem ParameterSmoothOn.div {Ω : Set (ℂ × E)} {F G : ℂ → E → ℂ}
    (hF : ParameterSmoothOn Ω F) (hG : ParameterSmoothOn Ω G) (hne : ∀ p∈Ω,G p.1 p.2≠0) :
    ParameterSmoothOn Ω (fun s y => F s y/G s y) := by
  simpa only [div_eq_mul_inv] using hF.mul (hG.inv hne)

theorem ParameterSmoothOn.pow {Ω : Set (ℂ × E)} {F : ℂ → E → ℂ}
    (hF : ParameterSmoothOn Ω F) (n : ℕ) :
    ParameterSmoothOn Ω (fun s y => (F s y)^n) := fun p hp =>
  ⟨(hF p hp).1.pow n,(hF p hp).2.pow n⟩

theorem ParameterSmoothOn.prod {Ω : Set (ℂ × E)} {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (F : ι → ℂ → E → ℂ) (hF : ∀ i∈S,ParameterSmoothOn Ω (F i)) :
    ParameterSmoothOn Ω (fun s y => ∏ i∈S,F i s y) := by
  intro p hp
  exact ⟨contDiffAt_finite_product S (fun i (z : ℂ × E) => F i z.1 z.2) p (fun i hi => (hF i hi p hp).1),
    DifferentiableAt.fun_finsetProd (fun i hi => (hF i hi p hp).2)⟩

theorem ParameterSmoothOn.complex_comp {Ω : Set (ℂ × E)} {F : ℂ → E → ℂ}
    (hF : ParameterSmoothOn Ω F) (g : ℂ → ℂ) (hg : ∀ p∈Ω,AnalyticAt ℂ g (F p.1 p.2)) :
    ParameterSmoothOn Ω (fun s y => g (F s y)) := by
  intro p hp
  exact ⟨((hg p hp).contDiffAt.restrict_scalars ℝ).comp p (hF p hp).1,
    (hg p hp).differentiableAt.comp p.1 (hF p hp).2⟩

theorem ParameterSmoothOn.continuousOn {Ω : Set (ℂ × E)} {F : ℂ → E → ℂ}
    (hF : ParameterSmoothOn Ω F) : ContinuousOn (Function.uncurry F) Ω :=
  fun p hp => (hF p hp).1.continuousAt.continuousWithinAt

theorem ParameterSmoothOn.parameter_analyticAt {Ω : Set (ℂ × E)} (hΩ : IsOpen Ω)
    {F : ℂ → E → ℂ} (hF : ParameterSmoothOn Ω F) {p : ℂ × E} (hp : p∈Ω) :
    AnalyticAt ℂ (fun s => F s p.2) p.1 := by
  let U := (fun s : ℂ => (s,p.2)) ⁻¹' Ω
  have hU : IsOpen U := hΩ.preimage (by fun_prop)
  exact DifferentiableOn.analyticAt (fun s hs => (hF (s,p.2) hs).2.differentiableWithinAt)
    (hU.mem_nhds hp)

end
end IsingBulk.Tail
