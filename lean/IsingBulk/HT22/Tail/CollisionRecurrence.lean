import IsingBulk.HT22.Tail.PhysicalRecurrence
import IsingBulk.HT22.Tail.VandermondeTransport
import IsingBulk.HT22.Transport.FieldNeighborhood.FixedVFramePullback

/-! Full collision filtration for the actual fixed-v mixed transport.
The generic squared-product directional identity is reused, not the old
field, old even determinant, or old transported scalar. -/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 Set
open scoped BigOperators ContDiff Topology
set_option backward.isDefEq.respectTransparency false

def materialFrame {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (F : ℂ → (Fin N → ℝ) → ℂ) (s : ℂ) (θ : Fin N → ℝ) : ℂ :=
  parameterFrame τ p m F s θ +
    ∑ a, residualField s (sourceCoordinate τ p m s θ) a*
      coordinateFrame τ p m a F s θ

theorem materialFrame_pullback {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : Differentiable ℝ p) (hm : Differentiable ℝ m)
    (s : ℂ) (θ : Fin N → ℝ) (hpoint : PreferredFramePoint τ δ p m s θ)
    (F : ℂ × (Fin N → ℂ) → ℂ)
    (hF : DifferentiableAt ℂ F (s,sourceCoordinate τ p m s θ)) :
    materialFrame τ p m
      (fun t x => F (t,sourceCoordinate τ p m t x)) s θ=
      fderiv ℂ F (s,sourceCoordinate τ p m s θ)
        (1,residualField s (sourceCoordinate τ p m s θ)) := by
  let B := residualField s (sourceCoordinate τ p m s θ)
  let T := fderiv ℂ F (s,sourceCoordinate τ p m s θ)
  unfold materialFrame
  rw [parameterFrame_pullback τ δ p m hp hm s θ hpoint F hF]
  simp_rw [coordinateFrame_pullback τ δ p m hp hm s θ hpoint F hF]
  have hvec : (1, (0 : Fin N → ℂ))+
      (∑ a, B a • ((0:ℂ),Pi.single a 1))=(1,B) := by
    ext i
    · simp [Prod.fst_sum]
    · simp [Prod.snd_sum,Finset.sum_apply,Pi.single_apply]
  change T (1,0)+(∑ a, B a*T (0,Pi.single a 1))=T (1,B)
  calc
    _ = T ((1,0)+(∑ a, B a • ((0:ℂ),Pi.single a 1))) := by
      rw [map_add,map_sum]
      simp only [map_smul,smul_eq_mul]
    _ = _ := by rw [hvec]

theorem materialFrame_eq {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (F : ℂ → (Fin N → ℝ) → ℂ) (s : ℂ) (θ : Fin N → ℝ) :
    materialFrame τ p m F s θ=
      deriv (fun t : ℂ => F t θ) s-
        ∑ i, angularField τ p m s θ i*
          deriv (fun x : ℝ => F s (Function.update θ i x)) (θ i) := by
  have hh := regularTransportStep_eq τ p m F s θ
  change materialFrame τ p m F s θ+_=_ at hh
  dsimp only [materialFrame] at hh ⊢
  linear_combination hh

theorem sourceVandermonde_material {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : Differentiable ℝ p) (hm : Differentiable ℝ m)
    (s : ℂ) (θ : Fin N → ℝ) (hpoint : PreferredFramePoint τ δ p m s θ)
    (C : Fin N → Fin N → ℂ)
    (hC : ∀ i j,
      residualField s (sourceCoordinate τ p m s θ) i-
        residualField s (sourceCoordinate τ p m s θ) j=
      (sourceCoordinate τ p m s θ i-sourceCoordinate τ p m s θ j)*C i j) :
    materialFrame τ p m
      (fun t x => preferredSquaredVandermonde (sourceCoordinate τ p m t x)) s θ=
      2*preferredUpperPairSum C*preferredSquaredVandermonde (sourceCoordinate τ p m s θ) := by
  let q := sourceCoordinate τ p m s θ
  have hd := (preferredSquaredVandermonde_analytic q).differentiableAt
  have hc : DifferentiableAt ℂ (fun z : ℂ × (Fin N → ℂ) => preferredSquaredVandermonde z.2) (s,q) :=
    DifferentiableAt.comp (f := fun z : ℂ × (Fin N → ℂ) => z.2)
      (g := preferredSquaredVandermonde) (s,q) hd differentiableAt_snd
  rw [materialFrame_pullback τ δ p m hp hm s θ hpoint
    (fun z => preferredSquaredVandermonde z.2) hc]
  have he := fderiv_comp (s,q) hd
    (show DifferentiableAt ℂ (Prod.snd : ℂ × (Fin N → ℂ) → (Fin N → ℂ)) (s,q) from differentiableAt_snd)
  change fderiv ℂ (preferredSquaredVandermonde ∘ Prod.snd) (s,q) _=_
  rw [he, fderiv_snd]
  change fderiv ℂ preferredSquaredVandermonde q (residualField s q)=_
  exact preferredSquaredVandermonde_directional q (residualField s q) C hC

/-- The literal regular generator preserves the complete squared
Vandermonde; the extra scalar is precisely twice the sum of pair factors. -/
theorem regularTransportStep_vandermonde {N : ℕ}
    (τ δ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (H : ℂ → (Fin N → ℝ) → ℂ) (s : ℂ) (θ : Fin N → ℝ)
    (hpoint : PreferredFramePoint τ δ p m s θ)
    (hHs : DifferentiableAt ℂ (fun t => H t θ) s)
    (hHθ : ∀ i, DifferentiableAt ℝ (fun x => H s (Function.update θ i x)) (θ i))
    (C : Fin N → Fin N → ℂ)
    (hC : ∀ i j,
      residualField s (sourceCoordinate τ p m s θ) i-
        residualField s (sourceCoordinate τ p m s θ) j=
      (sourceCoordinate τ p m s θ i-sourceCoordinate τ p m s θ j)*C i j) :
    regularTransportStep τ p m
      (fun t x => H t x*preferredSquaredVandermonde (sourceCoordinate τ p m t x)) s θ=
      (regularTransportStep τ p m H s θ+2*preferredUpperPairSum C*H s θ)*
        preferredSquaredVandermonde (sourceCoordinate τ p m s θ) := by
  let q := sourceCoordinate τ p m s θ
  have ha := preferredSquaredVandermonde_analytic q
  have hs0 : s≠0 := by intro he; have hh:=hpoint.trace_im; simp [he,temperatureTrace] at hh
  have hχs := sourceCoordinate_parameter_analyticAt τ p m s θ hs0 hpoint.upper
  have hχR := sourceCoordinate_contDiffAt τ p m hp hm s θ hpoint.trace_im hpoint.upper
  have hGs := ha.differentiableAt.comp s hχs.differentiableAt
  have hGR := (ha.contDiffAt.restrict_scalars ℝ).comp (s,θ) hχR
  have hGθ := preferredMixed_coordinate_differentiable
    (fun t x => preferredSquaredVandermonde (sourceCoordinate τ p m t x)) s θ hGR
  rw [regularTransportStep_mul τ p m H _ s θ hHs hGs hHθ hGθ,
    ←materialFrame_eq τ p m
      (fun t x => preferredSquaredVandermonde (sourceCoordinate τ p m t x)) s θ,
    sourceVandermonde_material τ δ p m (hp.differentiable (by simp))
      (hm.differentiable (by simp)) s θ hpoint C hC]
  ring

/-- The scalar recurrence after the full Vandermonde has been factored out.
Its pair-factor input will be the actual collective difference factor. -/
def vandermondeTransportStep {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (C : ℂ → (Fin N → ℝ) → Fin N → Fin N → ℂ)
    (H : ℂ → (Fin N → ℝ) → ℂ) (s : ℂ) (θ : Fin N → ℝ) : ℂ :=
  regularTransportStep τ p m H s θ+2*preferredUpperPairSum (C s θ)*H s θ

def vandermondeScalar {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (C : ℂ → (Fin N → ℝ) → Fin N → Fin N → ℂ)
    (A : ℂ → (Fin N → ℝ) → ℂ) : ℕ → ℂ → (Fin N → ℝ) → ℂ
  | 0 => A
  | j+1 => vandermondeTransportStep τ p m C (vandermondeScalar τ p m C A j)

 theorem vandermondeScalar_mixed {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (C : ℂ → (Fin N → ℝ) → Fin N → Fin N → ℂ)
    (A : ℂ → (Fin N → ℝ) → ℂ)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hV : ∀ i, PreferredMixedSmoothOn (fun z => angularField τ p m z.1 z.2 i) Ω)
    (hc : PreferredMixedSmoothOn (fun z => regularDivergence τ p m z.1 z.2) Ω)
    (hC : ∀ i j, PreferredMixedSmoothOn (fun z => C z.1 z.2 i j) Ω)
    (hA : PreferredMixedSmoothOn (fun z => A z.1 z.2) Ω) (j : ℕ) :
    PreferredMixedSmoothOn (fun z => vandermondeScalar τ p m C A j z.1 z.2) Ω := by
  have hsum : PreferredMixedSmoothOn (fun z => preferredUpperPairSum (C z.1 z.2)) Ω := by
    unfold preferredUpperPairSum
    apply PreferredMixedSmoothOn.sum
    intro i z hz
    exact ⟨ContDiffAt.sum (fun k _ => (hC i k z hz).1),
      DifferentiableAt.fun_sum (fun k _ => (hC i k z hz).2)⟩
  induction j with
  | zero => exact hA
  | succ j ih =>
    exact (regularTransportStep_mixed τ p m Ω hΩ hV hc _ ih).add
      (((PreferredMixedSmoothOn.const Ω 2).mul hsum).mul ih)

/-- Exact all-order full-Vandermonde factorization on a genuine source
chart. Only finitely many original functions need smoothness. -/
theorem regularTransportedScalar_vandermonde {N : ℕ}
    (τ δ : ℝ) (η p m r : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (C : ℂ → (Fin N → ℝ) → Fin N → Fin N → ℂ)
    (A : ℂ → (Fin N → ℝ) → ℂ)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hV : ∀ i, PreferredMixedSmoothOn (fun z => angularField τ p m z.1 z.2 i) Ω)
    (hc : PreferredMixedSmoothOn (fun z => regularDivergence τ p m z.1 z.2) Ω)
    (hC : ∀ i j, PreferredMixedSmoothOn (fun z => C z.1 z.2 i j) Ω)
    (hA : PreferredMixedSmoothOn (fun z => A z.1 z.2) Ω)
    (hfactor : ∀ z∈Ω, ∀ i j,
      residualField z.1 (sourceCoordinate τ p m z.1 z.2) i-
        residualField z.1 (sourceCoordinate τ p m z.1 z.2) j=
      (sourceCoordinate τ p m z.1 z.2 i-sourceCoordinate τ p m z.1 z.2 j)*C z.1 z.2 i j)
    (hseed : ∀ z∈Ω, regularSeed τ η p m r z.1 z.2=
      A z.1 z.2*preferredSquaredVandermonde (sourceCoordinate τ p m z.1 z.2))
    (j : ℕ) (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    regularTransportedScalar τ η p m r j s θ=
      vandermondeScalar τ p m C A j s θ*
        preferredSquaredVandermonde (sourceCoordinate τ p m s θ) := by
  induction j generalizing s θ with
  | zero => exact hseed (s,θ) hz
  | succ j ih =>
    have hmix := vandermondeScalar_mixed τ p m C A Ω hΩ hV hc hC hA j
    rw [regularTransportedScalar,
      regularTransportStep_congr_open τ p m _
        (fun t x => vandermondeScalar τ p m C A j t x*
          preferredSquaredVandermonde (sourceCoordinate τ p m t x))
        Ω hΩ (fun z hz => ih z.1 z.2 hz) s θ hz]
    exact regularTransportStep_vandermonde τ δ p m hp hm
      (vandermondeScalar τ p m C A j) s θ (hpoint (s,θ) hz)
      (hmix (s,θ) hz).2 (preferredMixed_coordinate_differentiable _ s θ (hmix (s,θ) hz).1)
      (C s θ) (hfactor (s,θ) hz)

end
end IsingBulk.HT22.Tail
