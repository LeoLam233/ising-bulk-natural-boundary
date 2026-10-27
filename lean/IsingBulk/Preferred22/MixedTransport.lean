import IsingBulk.Preferred22.MixedRegularity
import IsingBulk.Preferred22.MarkedTransportRecursion

/-! Finite base mixed regularity propagates through the actual scalar
transport and its explicit marked coefficients. This removes any need to
assume smoothness separately for infinitely many generated descendants. -/
namespace IsingBulk.Preferred22
noncomputable section
open Filter
open scoped Topology BigOperators ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem PreferredMixedSmoothOn.const (Ω : Set (ℂ × E)) (c : ℂ) :
    PreferredMixedSmoothOn (fun _ => c) Ω := fun _ _ => ⟨contDiffAt_const,differentiableAt_const _⟩

theorem PreferredMixedSmoothOn.add {A B : ℂ × E → ℂ} {Ω : Set (ℂ × E)}
    (hA : PreferredMixedSmoothOn A Ω) (hB : PreferredMixedSmoothOn B Ω) :
    PreferredMixedSmoothOn (fun z => A z+B z) Ω :=
  fun z hz => ⟨(hA z hz).1.add (hB z hz).1,(hA z hz).2.add (hB z hz).2⟩

theorem PreferredMixedSmoothOn.sub {A B : ℂ × E → ℂ} {Ω : Set (ℂ × E)}
    (hA : PreferredMixedSmoothOn A Ω) (hB : PreferredMixedSmoothOn B Ω) :
    PreferredMixedSmoothOn (fun z => A z-B z) Ω :=
  fun z hz => ⟨(hA z hz).1.sub (hB z hz).1,(hA z hz).2.sub (hB z hz).2⟩

theorem PreferredMixedSmoothOn.mul {A B : ℂ × E → ℂ} {Ω : Set (ℂ × E)}
    (hA : PreferredMixedSmoothOn A Ω) (hB : PreferredMixedSmoothOn B Ω) :
    PreferredMixedSmoothOn (fun z => A z*B z) Ω :=
  fun z hz => ⟨(hA z hz).1.mul (hB z hz).1,(hA z hz).2.mul (hB z hz).2⟩

theorem PreferredMixedSmoothOn.sum {ι : Type*} [Fintype ι]
    {A : ι → ℂ × E → ℂ} {Ω : Set (ℂ × E)}
    (hA : ∀ i, PreferredMixedSmoothOn (A i) Ω) :
    PreferredMixedSmoothOn (fun z => ∑ i, A i z) Ω := by
  intro z hz
  exact ⟨ContDiffAt.sum (fun i _ => (hA i z hz).1),
    DifferentiableAt.fun_sum (fun i _ => (hA i z hz).2)⟩

theorem PreferredMixedSmoothOn.congr {A B : ℂ × E → ℂ} {Ω : Set (ℂ × E)}
    (hA : PreferredMixedSmoothOn A Ω) (hΩ : IsOpen Ω) (he : ∀ z∈Ω, A z=B z) :
    PreferredMixedSmoothOn B Ω := by
  intro z hz
  have hh : A =ᶠ[𝓝 z] B := by
    filter_upwards [hΩ.mem_nhds hz] with x hx
    exact he x hx
  refine ⟨(hA z hz).1.congr_of_eventuallyEq hh.symm,?_⟩
  apply (hA z hz).2.congr_of_eventuallyEq
  exact (hh.comp_tendsto ((show Continuous (fun t : ℂ => (t,z.2)) by fun_prop).tendsto z.1)).symm

/-- An actual real coordinate derivative equals the joint real directional
derivative. This retains the original update-coordinate implementation. -/
theorem mixed_coordinate_deriv_eq {N : ℕ} (A : ℂ × (Fin N → ℝ) → ℂ)
    (z : ℂ × (Fin N → ℝ)) (i : Fin N) (hA : DifferentiableAt ℝ A z) :
    deriv (fun x : ℝ => A (z.1,Function.update z.2 i x)) (z.2 i)=
      fderiv ℝ A z (0,Pi.single i 1) := by
  have hg := (hasDerivAt_const (z.2 i) z.1).prodMk (hasDerivAt_update z.2 i (z.2 i))
  have hh := hA.hasFDerivAt.comp_hasDerivAt_of_eq (z.2 i) hg
    (by simp only [Function.update_eq_self,Prod.mk.eta])
  exact hh.deriv

theorem PreferredMixedSmoothOn.coordinate {N : ℕ}
    {A : ℂ × (Fin N → ℝ) → ℂ} {Ω : Set (ℂ × (Fin N → ℝ))}
    (hA : PreferredMixedSmoothOn A Ω) (hΩ : IsOpen Ω) (i : Fin N) :
    PreferredMixedSmoothOn
      (fun z => deriv (fun x : ℝ => A (z.1,Function.update z.2 i x)) (z.2 i)) Ω := by
  apply (hA.angular hΩ (Pi.single i 1)).congr hΩ
  intro z hz
  exact (mixed_coordinate_deriv_eq A z i ((hA z hz).1.differentiableAt (by simp))).symm

/-- The exact regular zero-order coefficient, namely divergence in the
actual q frame. -/
def preferredRegularDivergenceCoefficient {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (s : ℂ) (θ : Fin N → ℝ) : ℂ :=
  ∑ a, preferredCoordinateFrame τ p m a
    (fun t x => preferredResidualCollective t (preferredSourceCoordinate τ p m t x) a) s θ

theorem preferredRegularTransportStep_mixed {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hV : ∀ i, PreferredMixedSmoothOn
      (fun z => preferredSourceAngularField .right τ p m z.1 z.2 i) Ω)
    (hc : PreferredMixedSmoothOn (fun z => preferredRegularDivergenceCoefficient τ p m z.1 z.2) Ω)
    (A : ℂ → (Fin N → ℝ) → ℂ)
    (hA : PreferredMixedSmoothOn (fun z => A z.1 z.2) Ω) :
    PreferredMixedSmoothOn (fun z => preferredRegularTransportStep τ p m A z.1 z.2) Ω := by
  have hh := ((hA.parameter hΩ).sub (PreferredMixedSmoothOn.sum
    (fun i => (hV i).mul (hA.coordinate hΩ i)))).add (hc.mul hA)
  apply hh.congr hΩ
  intro z _
  exact (preferredRegularTransportStep_eq τ p m A z.1 z.2).symm

/-- Actual kernel-entry material derivatives inherit mixed regularity from
finitely many entry and angular-field functions. -/
theorem preferredKernelMaterialEntry_mixed {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hV : ∀ i, PreferredMixedSmoothOn
      (fun z => preferredSourceAngularField .right τ p m z.1 z.2 i) Ω)
    (hK : ∀ a : Fin N × Fin N, PreferredMixedSmoothOn
      (fun z => preferredSourceRegularKernel τ p m z.1 z.2 a.1 a.2) Ω)
    (a : Fin N × Fin N) :
    PreferredMixedSmoothOn (fun z => preferredKernelMaterialEntry τ p m z.1 z.2 a) Ω := by
  have hh := ((hK a).parameter hΩ).sub (PreferredMixedSmoothOn.sum
    (fun i => (hV i).mul ((hK a).coordinate hΩ i)))
  apply hh.congr hΩ
  intro z hz
  have hs : DifferentiableAt ℂ (fun t => preferredSourceRegularKernel τ p m t z.2) z.1 := by
    apply differentiableAt_pi.mpr
    intro i
    apply differentiableAt_pi.mpr
    intro j
    exact (hK (i,j) z hz).2
  have hθ (k : Fin N) : DifferentiableAt ℝ
      (fun x => preferredSourceRegularKernel τ p m z.1 (Function.update z.2 k x)) (z.2 k) := by
    apply differentiableAt_pi.mpr
    intro i
    apply differentiableAt_pi.mpr
    intro j
    have hx := (hK (i,j) z hz).1.differentiableAt (by simp)
    have hg := (hasDerivAt_const (z.2 k) z.1).prodMk (hasDerivAt_update z.2 k (z.2 k))
    exact (hx.hasFDerivAt.comp_hasDerivAt_of_eq (z.2 k) hg
      (by simp only [Function.update_eq_self,Prod.mk.eta])).differentiableAt
  have hsd := hs.hasDerivAt
  have hsd' := hasDerivAt_pi.mp (hasDerivAt_pi.mp hsd a.1) a.2
  have hθd (k : Fin N) :=
    hasDerivAt_pi.mp (hasDerivAt_pi.mp (hθ k).hasDerivAt a.1) a.2
  unfold preferredKernelMaterialEntry
  rw [hsd'.deriv]
  simp_rw [(hθd _).deriv]

/-- Only these finitely many base source functions need mixed regularity.
There is no assumption on any generated coefficient or on its norm. -/
def PreferredMarkedBaseSmoothness {N : ℕ} (τ : ℝ) (η p m r : ℝ → ℝ)
    (Ω : Set (ℂ × (Fin N → ℝ))) : Prop :=
  (∀ i, PreferredMixedSmoothOn (fun z => preferredSourceAngularField .right τ p m z.1 z.2 i) Ω) ∧
  PreferredMixedSmoothOn (fun z => preferredRegularDivergenceCoefficient τ p m z.1 z.2) Ω ∧
  (∀ a : Fin N × Fin N, PreferredMixedSmoothOn
    (fun z => preferredSourceRegularKernel τ p m z.1 z.2 a.1 a.2) Ω) ∧
  PreferredMixedSmoothOn (fun z => preferredRegularSeedCoefficient τ η p m r z.1 z.2) Ω

theorem preferredWordCoefficient_mixed {N : ℕ} (τ : ℝ) (η p m r : ℝ → ℝ)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hb : PreferredMarkedBaseSmoothness τ η p m r Ω)
    (j : ℕ) (w : PreferredMarkedWord N j) :
    PreferredMixedSmoothOn (fun z => preferredWordCoefficient τ η p m r j w z.1 z.2) Ω := by
  induction j with
  | zero => exact hb.2.2.2
  | succ j ih =>
    cases hw : w 0 with
    | none =>
      simpa only [preferredWordCoefficient,hw] using
        preferredRegularTransportStep_mixed τ p m Ω hΩ hb.1 hb.2.1
          (preferredWordCoefficient τ η p m r j (Fin.tail w)) (ih (Fin.tail w))
    | some a =>
      simpa only [preferredWordCoefficient,hw] using
        (ih (Fin.tail w)).mul (preferredKernelMaterialEntry_mixed τ p m Ω hΩ hb.1 hb.2.2.1 a)

theorem preferredWordDifferentiability_of_base {N : ℕ} (τ : ℝ) (η p m r : ℝ → ℝ)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hb : PreferredMarkedBaseSmoothness τ η p m r Ω) :
    PreferredWordDifferentiability τ η p m r Ω := by
  intro z hz
  have hcoord {F : ℂ × (Fin N → ℝ) → ℂ} (hF : PreferredMixedSmoothOn F Ω) (i : Fin N) :
      DifferentiableAt ℝ (fun x => F (z.1,Function.update z.2 i x)) (z.2 i) := by
    have hh := (hF z hz).1.differentiableAt (by simp)
    have hg := (hasDerivAt_const (z.2 i) z.1).prodMk (hasDerivAt_update z.2 i (z.2 i))
    exact (hh.hasFDerivAt.comp_hasDerivAt_of_eq (z.2 i) hg
      (by simp only [Function.update_eq_self,Prod.mk.eta])).differentiableAt
  refine ⟨?_,?_,?_⟩
  · apply differentiableAt_pi.mpr
    intro i
    apply differentiableAt_pi.mpr
    intro j
    exact (hb.2.2.1 (i,j) z hz).2
  · intro i
    apply differentiableAt_pi.mpr
    intro a
    apply differentiableAt_pi.mpr
    intro b
    exact hcoord (hb.2.2.1 (a,b)) i
  · intro j w
    have hh := preferredWordCoefficient_mixed τ η p m r Ω hΩ hb j w
    exact ⟨(hh z hz).2,hcoord hh⟩

theorem preferredRegularTransportedScalar_word_expansion_of_base {N : ℕ}
    (τ : ℝ) (η p m r : ℝ → ℝ) (Ω : Set (ℂ × (Fin N → ℝ)))
    (hΩ : IsOpen Ω) (hb : PreferredMarkedBaseSmoothness τ η p m r Ω)
    (j : ℕ) (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    preferredRegularTransportedScalar τ η p m r j s θ=preferredWordSum τ η p m r j s θ :=
  preferredRegularTransportedScalar_word_expansion τ η p m r Ω hΩ
    (preferredWordDifferentiability_of_base τ η p m r Ω hΩ hb) j s θ hz

end
end IsingBulk.Preferred22
