import IsingBulk.Preferred22.FrameAlgebra

/-! Full squared-Vandermonde transport, including every partial collision.
The factorization is algebraic after the genuine source-frame identities;
it never divides by a pair difference. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set
open scoped BigOperators ContDiff Topology
set_option backward.isDefEq.respectTransparency false

def preferredSquaredVandermonde {N : ℕ} (q : Fin N → ℂ) : ℂ :=
  ∏ i, ∏ j ∈ Finset.Ioi i, (q i-q j)^2

def preferredUpperPairSum {N : ℕ} (C : Fin N → Fin N → ℂ) : ℂ :=
  ∑ i, ∑ j ∈ Finset.Ioi i, C i j

theorem preferredSquaredVandermonde_analytic {N : ℕ} (q : Fin N → ℂ) :
    AnalyticAt ℂ preferredSquaredVandermonde q := by
  unfold preferredSquaredVandermonde
  apply Finset.analyticAt_fun_prod
  intro i _
  apply Finset.analyticAt_fun_prod
  intro j _
  exact (((ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ).analyticAt q).sub
    ((ContinuousLinearMap.proj j : (Fin N → ℂ) →L[ℂ] ℂ).analyticAt q)).pow 2

/-- A multiplicative derivative identity with no nonvanishing premise. -/
theorem hasDerivAt_finset_prod_factor {ι : Type*} (S : Finset ι)
    (f : ι → ℂ → ℂ) (c : ι → ℂ) (x : ℂ)
    (hf : ∀ i∈S, HasDerivAt (f i) (c i*f i x) x) :
    HasDerivAt (fun t => ∏ i∈S, f i t)
      ((∑ i∈S, c i)*(∏ i∈S, f i x)) x := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using hasDerivAt_const x (1:ℂ)
  | @insert i S hi ih =>
    have ha := hf i (Finset.mem_insert_self ..)
    have hb := ih (fun k hk => hf k (Finset.mem_insert_of_mem hk))
    simp only [Finset.prod_insert hi,Finset.sum_insert hi]
    convert ha.fun_mul hb using 1
    ring

/-- The directional derivative retains every collision factor. -/
theorem preferredSquaredVandermonde_directional {N : ℕ}
    (q v : Fin N → ℂ) (C : Fin N → Fin N → ℂ)
    (hC : ∀ i j, v i-v j=(q i-q j)*C i j) :
    fderiv ℂ preferredSquaredVandermonde q v =
      2*preferredUpperPairSum C*preferredSquaredVandermonde q := by
  have hentry (i j : Fin N) :
      HasDerivAt (fun t : ℂ => ((q i+t*v i)-(q j+t*v j))^2)
        ((2*C i j)*(q i-q j)^2) 0 := by
    have hh := (((hasDerivAt_const 0 (q i)).fun_add
      ((hasDerivAt_id (0:ℂ)).mul_const (v i))).fun_sub
      ((hasDerivAt_const 0 (q j)).fun_add
        ((hasDerivAt_id (0:ℂ)).mul_const (v j)))).fun_pow 2
    convert hh using 1
    all_goals simp only [id_eq, zero_mul, add_zero, zero_add, one_mul, Nat.reduceSub,
      pow_one, Nat.cast_ofNat]
    rw [hC]
    ring
  have hrow (i : Fin N) := hasDerivAt_finset_prod_factor (Finset.Ioi i)
    (fun j t => ((q i+t*v i)-(q j+t*v j))^2) (fun j => 2*C i j) 0
    (fun j _ => by simpa using hentry i j)
  have hprod := hasDerivAt_finset_prod_factor (Finset.univ : Finset (Fin N))
    (fun i t => ∏ j∈Finset.Ioi i, ((q i+t*v i)-(q j+t*v j))^2)
    (fun i => ∑ j∈Finset.Ioi i, 2*C i j) 0
    (fun i _ => hrow i)
  have hline : HasDerivAt (fun t : ℂ => q+t • v) v 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    change HasDerivAt (fun t : ℂ => q i+t*v i) (v i) 0
    simpa only [zero_add,one_mul,id_eq] using
      (hasDerivAt_const 0 (q i)).fun_add ((hasDerivAt_id (0:ℂ)).mul_const (v i))
  have hchain := (preferredSquaredVandermonde_analytic q).differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq
    0 hline (by simp)
  have he := hchain.unique hprod
  simpa only [preferredSquaredVandermonde,preferredUpperPairSum,Pi.add_apply,
    Pi.smul_apply,smul_eq_mul,zero_mul,add_zero,Finset.mul_sum] using he

def preferredMaterialFrame {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (F : ℂ → (Fin N → ℝ) → ℂ) (s : ℂ) (θ : Fin N → ℝ) : ℂ :=
  preferredParameterFrame τ p m F s θ +
    ∑ a, preferredResidualCollective s (preferredSourceCoordinate τ p m s θ) a*
      preferredCoordinateFrame τ p m a F s θ

theorem preferredMaterialFrame_pullback {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : Differentiable ℝ p) (hm : Differentiable ℝ m)
    (s : ℂ) (θ : Fin N → ℝ) (hpoint : PreferredFramePoint τ δ p m s θ)
    (F : ℂ × (Fin N → ℂ) → ℂ)
    (hF : DifferentiableAt ℂ F (s,preferredSourceCoordinate τ p m s θ)) :
    preferredMaterialFrame τ p m
      (fun t x => F (t,preferredSourceCoordinate τ p m t x)) s θ=
      fderiv ℂ F (s,preferredSourceCoordinate τ p m s θ)
        (1,preferredResidualCollective s (preferredSourceCoordinate τ p m s θ)) := by
  let B := preferredResidualCollective s (preferredSourceCoordinate τ p m s θ)
  let T := fderiv ℂ F (s,preferredSourceCoordinate τ p m s θ)
  unfold preferredMaterialFrame
  rw [preferredParameterFrame_pullback τ δ p m hp hm s θ hpoint F hF]
  simp_rw [preferredCoordinateFrame_pullback τ δ p m hp hm s θ hpoint F hF]
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

theorem preferredMaterialFrame_eq {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (F : ℂ → (Fin N → ℝ) → ℂ) (s : ℂ) (θ : Fin N → ℝ) :
    preferredMaterialFrame τ p m F s θ=
      deriv (fun t : ℂ => F t θ) s-
        ∑ i, preferredSourceAngularField .right τ p m s θ i*
          deriv (fun x : ℝ => F s (Function.update θ i x)) (θ i) := by
  have hh := preferredRegularTransportStep_eq τ p m F s θ
  change preferredMaterialFrame τ p m F s θ+_=_ at hh
  dsimp only [preferredMaterialFrame] at hh ⊢
  linear_combination hh

theorem preferredSourceVandermonde_material {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : Differentiable ℝ p) (hm : Differentiable ℝ m)
    (s : ℂ) (θ : Fin N → ℝ) (hpoint : PreferredFramePoint τ δ p m s θ)
    (C : Fin N → Fin N → ℂ)
    (hC : ∀ i j,
      preferredResidualCollective s (preferredSourceCoordinate τ p m s θ) i-
        preferredResidualCollective s (preferredSourceCoordinate τ p m s θ) j=
      (preferredSourceCoordinate τ p m s θ i-preferredSourceCoordinate τ p m s θ j)*C i j) :
    preferredMaterialFrame τ p m
      (fun t x => preferredSquaredVandermonde (preferredSourceCoordinate τ p m t x)) s θ=
      2*preferredUpperPairSum C*preferredSquaredVandermonde (preferredSourceCoordinate τ p m s θ) := by
  let q := preferredSourceCoordinate τ p m s θ
  have hd := (preferredSquaredVandermonde_analytic q).differentiableAt
  have hc : DifferentiableAt ℂ (fun z : ℂ × (Fin N → ℂ) => preferredSquaredVandermonde z.2) (s,q) :=
    DifferentiableAt.comp (f := fun z : ℂ × (Fin N → ℂ) => z.2)
      (g := preferredSquaredVandermonde) (s,q) hd differentiableAt_snd
  rw [preferredMaterialFrame_pullback τ δ p m hp hm s θ hpoint
    (fun z => preferredSquaredVandermonde z.2) hc]
  have he := fderiv_comp (s,q) hd
    (show DifferentiableAt ℂ (Prod.snd : ℂ × (Fin N → ℂ) → (Fin N → ℂ)) (s,q) from differentiableAt_snd)
  change fderiv ℂ (preferredSquaredVandermonde ∘ Prod.snd) (s,q) _=_
  rw [he, fderiv_snd]
  change fderiv ℂ preferredSquaredVandermonde q (preferredResidualCollective s q)=_
  exact preferredSquaredVandermonde_directional q (preferredResidualCollective s q) C hC

/-- The literal regular generator preserves the complete squared
Vandermonde; the extra scalar is precisely twice the sum of pair factors. -/
theorem preferredRegularTransportStep_vandermonde {N : ℕ}
    (τ δ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (H : ℂ → (Fin N → ℝ) → ℂ) (s : ℂ) (θ : Fin N → ℝ)
    (hpoint : PreferredFramePoint τ δ p m s θ)
    (hHs : DifferentiableAt ℂ (fun t => H t θ) s)
    (hHθ : ∀ i, DifferentiableAt ℝ (fun x => H s (Function.update θ i x)) (θ i))
    (C : Fin N → Fin N → ℂ)
    (hC : ∀ i j,
      preferredResidualCollective s (preferredSourceCoordinate τ p m s θ) i-
        preferredResidualCollective s (preferredSourceCoordinate τ p m s θ) j=
      (preferredSourceCoordinate τ p m s θ i-preferredSourceCoordinate τ p m s θ j)*C i j) :
    preferredRegularTransportStep τ p m
      (fun t x => H t x*preferredSquaredVandermonde (preferredSourceCoordinate τ p m t x)) s θ=
      (preferredRegularTransportStep τ p m H s θ+2*preferredUpperPairSum C*H s θ)*
        preferredSquaredVandermonde (preferredSourceCoordinate τ p m s θ) := by
  let q := preferredSourceCoordinate τ p m s θ
  have ha := preferredSquaredVandermonde_analytic q
  have hχs := preferredSourceCoordinate_parameter_analyticAt τ p m s θ hpoint.trace_im hpoint.upper
  have hχR := preferredSourceCoordinate_contDiffAt τ p m hp hm s θ hpoint.trace_im hpoint.upper
  have hGs := ha.differentiableAt.comp s hχs.differentiableAt
  have hGR := (ha.contDiffAt.restrict_scalars ℝ).comp (s,θ) hχR
  have hGθ := preferredMixed_coordinate_differentiable
    (fun t x => preferredSquaredVandermonde (preferredSourceCoordinate τ p m t x)) s θ hGR
  rw [preferredRegularTransportStep_mul τ p m H _ s θ hHs hGs hHθ hGθ,
    ←preferredMaterialFrame_eq τ p m
      (fun t x => preferredSquaredVandermonde (preferredSourceCoordinate τ p m t x)) s θ,
    preferredSourceVandermonde_material τ δ p m (hp.differentiable (by simp))
      (hm.differentiable (by simp)) s θ hpoint C hC]
  ring

/-- The scalar recurrence after the full Vandermonde has been factored out.
Its pair-factor input will be the actual collective difference factor. -/
def preferredVandermondeTransportStep {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (C : ℂ → (Fin N → ℝ) → Fin N → Fin N → ℂ)
    (H : ℂ → (Fin N → ℝ) → ℂ) (s : ℂ) (θ : Fin N → ℝ) : ℂ :=
  preferredRegularTransportStep τ p m H s θ+2*preferredUpperPairSum (C s θ)*H s θ

def preferredVandermondeScalar {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (C : ℂ → (Fin N → ℝ) → Fin N → Fin N → ℂ)
    (A : ℂ → (Fin N → ℝ) → ℂ) : ℕ → ℂ → (Fin N → ℝ) → ℂ
  | 0 => A
  | j+1 => preferredVandermondeTransportStep τ p m C (preferredVandermondeScalar τ p m C A j)

 theorem preferredVandermondeScalar_mixed {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (C : ℂ → (Fin N → ℝ) → Fin N → Fin N → ℂ)
    (A : ℂ → (Fin N → ℝ) → ℂ)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hV : ∀ i, PreferredMixedSmoothOn (fun z => preferredSourceAngularField .right τ p m z.1 z.2 i) Ω)
    (hc : PreferredMixedSmoothOn (fun z => preferredRegularDivergenceCoefficient τ p m z.1 z.2) Ω)
    (hC : ∀ i j, PreferredMixedSmoothOn (fun z => C z.1 z.2 i j) Ω)
    (hA : PreferredMixedSmoothOn (fun z => A z.1 z.2) Ω) (j : ℕ) :
    PreferredMixedSmoothOn (fun z => preferredVandermondeScalar τ p m C A j z.1 z.2) Ω := by
  have hsum : PreferredMixedSmoothOn (fun z => preferredUpperPairSum (C z.1 z.2)) Ω := by
    unfold preferredUpperPairSum
    apply PreferredMixedSmoothOn.sum
    intro i z hz
    exact ⟨ContDiffAt.sum (fun k _ => (hC i k z hz).1),
      DifferentiableAt.fun_sum (fun k _ => (hC i k z hz).2)⟩
  induction j with
  | zero => exact hA
  | succ j ih =>
    exact (preferredRegularTransportStep_mixed τ p m Ω hΩ hV hc _ ih).add
      (((PreferredMixedSmoothOn.const Ω 2).mul hsum).mul ih)

/-- Exact all-order full-Vandermonde factorization on a genuine source
chart. Only finitely many original functions need smoothness. -/
theorem preferredRegularTransportedScalar_vandermonde {N : ℕ}
    (τ δ : ℝ) (η p m r : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (C : ℂ → (Fin N → ℝ) → Fin N → Fin N → ℂ)
    (A : ℂ → (Fin N → ℝ) → ℂ)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hV : ∀ i, PreferredMixedSmoothOn (fun z => preferredSourceAngularField .right τ p m z.1 z.2 i) Ω)
    (hc : PreferredMixedSmoothOn (fun z => preferredRegularDivergenceCoefficient τ p m z.1 z.2) Ω)
    (hC : ∀ i j, PreferredMixedSmoothOn (fun z => C z.1 z.2 i j) Ω)
    (hA : PreferredMixedSmoothOn (fun z => A z.1 z.2) Ω)
    (hfactor : ∀ z∈Ω, ∀ i j,
      preferredResidualCollective z.1 (preferredSourceCoordinate τ p m z.1 z.2) i-
        preferredResidualCollective z.1 (preferredSourceCoordinate τ p m z.1 z.2) j=
      (preferredSourceCoordinate τ p m z.1 z.2 i-preferredSourceCoordinate τ p m z.1 z.2 j)*C z.1 z.2 i j)
    (hseed : ∀ z∈Ω, preferredRegularSeed τ η p m r z.1 z.2=
      A z.1 z.2*preferredSquaredVandermonde (preferredSourceCoordinate τ p m z.1 z.2))
    (j : ℕ) (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    preferredRegularTransportedScalar τ η p m r j s θ=
      preferredVandermondeScalar τ p m C A j s θ*
        preferredSquaredVandermonde (preferredSourceCoordinate τ p m s θ) := by
  induction j generalizing s θ with
  | zero => exact hseed (s,θ) hz
  | succ j ih =>
    have hmix := preferredVandermondeScalar_mixed τ p m C A Ω hΩ hV hc hC hA j
    rw [preferredRegularTransportedScalar,
      preferredRegularTransportStep_congr_open τ p m _
        (fun t x => preferredVandermondeScalar τ p m C A j t x*
          preferredSquaredVandermonde (preferredSourceCoordinate τ p m t x))
        Ω hΩ (fun z hz => ih z.1 z.2 hz) s θ hz]
    exact preferredRegularTransportStep_vandermonde τ δ p m hp hm
      (preferredVandermondeScalar τ p m C A j) s θ (hpoint (s,θ) hz)
      (hmix (s,θ) hz).2 (preferredMixed_coordinate_differentiable _ s θ (hmix (s,θ) hz).1)
      (C s θ) (hfactor (s,θ) hz)

end
end IsingBulk.Preferred22
