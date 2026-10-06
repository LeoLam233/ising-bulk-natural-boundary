import IsingBulk.Tail.ParameterSmoothAlgebra
import Mathlib.Analysis.Calculus.Deriv.Support

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Lie Set Filter
open scoped Topology ContDiff BigOperators

theorem lieStep_zero_off_closed {n : ℕ} (K : Set (AngularSpace n)) (hK : IsClosed K)
    (V : ℂ → AngularSpace n → Fin (n+1) → ℂ) (A : ℂ → AngularSpace n → ℂ)
    (hA : ∀ s x,x∉K → A s x=0) (s : ℂ) (x : AngularSpace n) (hx : x∉K) :
    lieStep V A s x=0 := by
  have hs : (fun t => A t x)=(fun _ => (0:ℂ)) := funext (fun t => hA t x hx)
  have hflux (i : Fin (n+1)) : tsupport (fun y => V s y i*A s y)⊆K := by
    apply closure_minimal _ hK
    intro y hy
    by_contra hn
    exact hy (by simp [hA s y hn])
  unfold lieStep divergence
  rw [hs,deriv_const]
  have hzero (i : Fin (n+1)) : fderiv ℝ (fun y => V s y i*A s y) x=0 :=
    fderiv_of_notMem_tsupport (𝕜 := ℝ) (fun hh => hx (hflux i hh))
  simp only [hzero,zero_apply,Finset.sum_const_zero,sub_zero]

theorem iterate_lieStep_zero_off_weight {n : ℕ}
    (V : ℂ → AngularSpace n → Fin (n+1) → ℂ) (D : ℂ → AngularSpace n → ℂ)
    (w : AngularSpace n → ℂ) (k : ℕ) :
    ∀ s x,x∉tsupport w → ((lieStep V)^[k] (fun s x => w x*D s x)) s x=0 := by
  induction k with
  | zero => intro s x hx; simp [image_eq_zero_of_notMem_tsupport hx]
  | succ k ih =>
    intro s x hx
    rw [Function.iterate_succ_apply']
    exact lieStep_zero_off_closed (tsupport w) (isClosed_tsupport w) V _ ih s x hx

theorem parameterSmooth_glue_closed_support {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Set (ℂ × E)} {U : Set ℂ} {K : Set E} (hK : IsClosed K)
    (F : ℂ → E → ℂ) (hF : ParameterSmoothOn Ω F) (hcover : U ×ˢ K⊆Ω)
    (hzero : ∀ s x,x∉K → F s x=0) : ParameterSmoothOn (U ×ˢ Set.univ) F := by
  intro p hp
  by_cases hx : p.2∈K
  · exact hF p (hcover ⟨hp.1,hx⟩)
  · have he : Function.uncurry F =ᶠ[𝓝 p] (fun _ => (0:ℂ)) := by
      filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (hK.isOpen_compl.mem_nhds hx)] with z hz
      exact hzero z.1 z.2 hz
    have hslice : (fun s => F s p.2)=(fun _ => (0:ℂ)) := funext (fun s => hzero s p.2 hx)
    refine ⟨contDiffAt_const.congr_of_eventuallyEq he,?_⟩
    rw [hslice]
    exact differentiableAt_const 0

theorem supported_weighted_lie_stages_regular {n : ℕ} {Ω : Set (ℂ × AngularSpace n)}
    (hΩ : IsOpen Ω) (U : Set ℂ) (V : ℂ → AngularSpace n → Fin (n+1) → ℂ)
    (D : ℂ → AngularSpace n → ℂ) (w : AngularSpace n → ℂ)
    (hw : ContDiff ℝ ∞ w) (hD : ParameterSmoothOn Ω D)
    (hV : ∀ i,ParameterSmoothOn Ω (fun s x => V s x i))
    (hcover : U ×ˢ tsupport w⊆Ω) (k : ℕ) :
    ParameterSmoothOn (U ×ˢ Set.univ) ((lieStep V)^[k] (fun s x => w x*D s x)) ∧
      ∀ i,ParameterSmoothOn (U ×ˢ Set.univ)
        (fun s x => V s x i*((lieStep V)^[k] (fun s x => w x*D s x)) s x) := by
  have hStage := ((ParameterSmoothOn.angular Ω w hw).mul hD).iterate_lieStep hΩ V _ hV k
  have hz := iterate_lieStep_zero_off_weight V D w k
  refine ⟨parameterSmooth_glue_closed_support (isClosed_tsupport w) _ hStage hcover hz,?_⟩
  intro i
  exact parameterSmooth_glue_closed_support (isClosed_tsupport w) _ ((hV i).mul hStage) hcover
    (fun s x hx => by rw [hz s x hx,mul_zero])

end
end IsingBulk.Tail
