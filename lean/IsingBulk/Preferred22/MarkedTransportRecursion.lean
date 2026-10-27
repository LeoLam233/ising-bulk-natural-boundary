import IsingBulk.Preferred22.MarkedTransport
import Mathlib.Data.Fintype.BigOperators

/-! A finite, source-defined marked expansion of the actual regular scalar
recurrence. Its coefficients are computed from the literal source operator,
not existential placeholders. The theorem explicitly retains the local
coefficient differentiability cut; uniform loss bounds and the physical
Piola identification are not assumed to follow from the combinatorics. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators ContDiff Matrix.Norms.Elementwise Topology
open Filter
set_option backward.isDefEq.respectTransparency false

abbrev PreferredMarkedWord (N j : ℕ) := Fin j → Option (Fin N × Fin N)

def preferredWordMarks {N : ℕ} : (j : ℕ) → PreferredMarkedWord N j → List (Fin N × Fin N)
  | 0, _ => []
  | j+1, w => match w 0 with
    | none => preferredWordMarks j (Fin.tail w)
    | some a => a::preferredWordMarks j (Fin.tail w)

/-- The worst scalar loss assigned by the actual two product-rule branches.
It is a combinatorial degree; its analytic norm bound is still separate. -/
def preferredWordLoss {N : ℕ} : (j : ℕ) → PreferredMarkedWord N j → ℕ
  | 0, _ => 0
  | j+1, w => match w 0 with
    | none => preferredWordLoss j (Fin.tail w)+2
    | some _ => preferredWordLoss j (Fin.tail w)+1

def preferredWordCoefficient {N : ℕ} (τ : ℝ) (η p m r : ℝ → ℝ) :
    (j : ℕ) → PreferredMarkedWord N j → ℂ → (Fin N → ℝ) → ℂ
  | 0, _ => preferredRegularSeedCoefficient τ η p m r
  | j+1, w => match w 0 with
    | none => preferredRegularTransportStep τ p m
        (preferredWordCoefficient τ η p m r j (Fin.tail w))
    | some a => fun s θ => preferredWordCoefficient τ η p m r j (Fin.tail w) s θ *
        preferredKernelMaterialEntry τ p m s θ a

def preferredWordSum {N : ℕ} (τ : ℝ) (η p m r : ℝ → ℝ)
    (j : ℕ) (s : ℂ) (θ : Fin N → ℝ) : ℂ :=
  ∑ w : PreferredMarkedWord N j, preferredWordCoefficient τ η p m r j w s θ *
    preferredMarkedMinor (preferredSourceRegularKernel τ p m s θ) (preferredWordMarks j w)

theorem preferredWordMarks_length {N : ℕ} (j : ℕ) (w : PreferredMarkedWord N j) :
    (preferredWordMarks j w).length ≤ j := by
  induction j with
  | zero => simp [preferredWordMarks]
  | succ j ih =>
    cases hw : w 0 with
    | none => simpa only [preferredWordMarks,hw] using (ih (Fin.tail w)).trans (Nat.le_succ j)
    | some a => simpa only [preferredWordMarks,hw,List.length_cons] using Nat.succ_le_succ (ih (Fin.tail w))

theorem preferredWordLoss_budget {N : ℕ} (j : ℕ) (w : PreferredMarkedWord N j) :
    preferredWordLoss j w+(preferredWordMarks j w).length=2*j := by
  induction j with
  | zero => simp [preferredWordLoss,preferredWordMarks]
  | succ j ih =>
    cases hw : w 0 with
    | none => simp only [preferredWordLoss,preferredWordMarks,hw]; have hh:=ih (Fin.tail w); omega
    | some a => simp only [preferredWordLoss,preferredWordMarks,hw,List.length_cons]; have hh:=ih (Fin.tail w); omega

theorem preferredWord_card (N j : ℕ) : Fintype.card (PreferredMarkedWord N j)=(N^2+1)^j := by
  simp [PreferredMarkedWord,Nat.pow_two]

theorem preferredWord_polynomial_count (j : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ N : ℕ, 0<N → (Fintype.card (PreferredMarkedWord N j):ℝ) ≤ C*(N:ℝ)^(2*j) := by
  refine ⟨2^j,by positivity,?_⟩
  intro N hN
  have hb : N^2+1≤2*N^2 := by nlinarith [Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hN)]
  have hh : (N^2+1)^j≤2^j*N^(2*j) := by
    calc
      _ ≤ (2*N^2)^j := Nat.pow_le_pow_left hb j
      _ = _ := by rw [mul_pow,←pow_mul]
  rw [preferredWord_card]
  exact_mod_cast hh

theorem preferredWordSum_zero {N : ℕ} (τ : ℝ) (η p m r : ℝ → ℝ)
    (s : ℂ) (θ : Fin N → ℝ) : preferredWordSum τ η p m r 0 s θ=preferredRegularSeed τ η p m r s θ := by
  rw [preferredRegularSeed_eq_empty_minor]
  simp [preferredWordSum,preferredWordCoefficient,preferredWordMarks]

/-- The actual generator is local in the product of the parameter and real
angular variables; no analyticity is needed to transport germ equalities. -/
theorem preferredRegularTransportStep_congr_open {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (A G : ℂ → (Fin N → ℝ) → ℂ) (Ω : Set (ℂ × (Fin N → ℝ)))
    (hΩ : IsOpen Ω) (hEq : ∀ z ∈ Ω, A z.1 z.2=G z.1 z.2)
    (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    preferredRegularTransportStep τ p m A s θ=preferredRegularTransportStep τ p m G s θ := by
  classical
  have he : (fun z : ℂ × (Fin N → ℝ) => A z.1 z.2) =ᶠ[𝓝 (s,θ)] (fun z => G z.1 z.2) := by
    filter_upwards [hΩ.mem_nhds hz] with z hz
    exact hEq z hz
  have hs : deriv (fun t : ℂ => A t θ) s=deriv (fun t : ℂ => G t θ) s := by
    exact (he.comp_tendsto ((show Continuous (fun t : ℂ => (t,θ)) by fun_prop).tendsto s)).deriv_eq
  have hx (i : Fin N) : deriv (fun x : ℝ => A s (Function.update θ i x)) (θ i)=
      deriv (fun x : ℝ => G s (Function.update θ i x)) (θ i) := by
    have hc : Continuous (fun x : ℝ => (s,Function.update θ i x)) :=
      by fun_prop
    have ht : Tendsto (fun x : ℝ => (s,Function.update θ i x)) (𝓝 (θ i)) (𝓝 (s,θ)) := by
      simpa only [Function.update_eq_self] using hc.tendsto (θ i)
    exact (he.comp_tendsto ht).deriv_eq
  rw [preferredRegularTransportStep_eq,preferredRegularTransportStep_eq,hs,hEq (s,θ) hz]
  simp_rw [hx]

theorem preferredRegularTransportStep_sum {N : ℕ} {ι : Type*} [Fintype ι]
    (τ : ℝ) (p m : ℝ → ℝ) (F : ι → ℂ → (Fin N → ℝ) → ℂ)
    (s : ℂ) (θ : Fin N → ℝ)
    (hs : ∀ a, DifferentiableAt ℂ (fun t => F a t θ) s)
    (hθ : ∀ a i, DifferentiableAt ℝ (fun x => F a s (Function.update θ i x)) (θ i)) :
    preferredRegularTransportStep τ p m (fun t x => ∑ a, F a t x) s θ =
      ∑ a, preferredRegularTransportStep τ p m (F a) s θ := by
  classical
  simp_rw [preferredRegularTransportStep_eq]
  rw [deriv_fun_sum (fun a _ => hs a)]
  simp_rw [deriv_fun_sum (fun a _ => hθ a _)]
  simp only [Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_comm]

theorem preferredWordSum_succ {N : ℕ} (τ : ℝ) (η p m r : ℝ → ℝ)
    (j : ℕ) (s : ℂ) (θ : Fin N → ℝ)
    (hAs : ∀ w : PreferredMarkedWord N j,
      DifferentiableAt ℂ (fun t => preferredWordCoefficient τ η p m r j w t θ) s)
    (hAθ : ∀ (w : PreferredMarkedWord N j) i, DifferentiableAt ℝ
      (fun x => preferredWordCoefficient τ η p m r j w s (Function.update θ i x)) (θ i))
    (hKs : DifferentiableAt ℂ (fun t => preferredSourceRegularKernel τ p m t θ) s)
    (hKθ : ∀ i, DifferentiableAt ℝ
      (fun x => preferredSourceRegularKernel τ p m s (Function.update θ i x)) (θ i)) :
    preferredWordSum τ η p m r (j+1) s θ =
      ∑ w : PreferredMarkedWord N j, preferredRegularTransportStep τ p m
        (fun t x => preferredWordCoefficient τ η p m r j w t x *
          preferredMarkedMinor (preferredSourceRegularKernel τ p m t x) (preferredWordMarks j w)) s θ := by
  classical
  simp_rw [preferredRegularTransportStep_marked τ p m _ s θ _ (hAs _) (hAθ _) hKs hKθ]
  unfold preferredWordSum
  rw [← (Fin.consEquiv (fun _ : Fin (j+1) => Option (Fin N × Fin N))).sum_comp]
  have hcons (a : Option (Fin N × Fin N)) (w : PreferredMarkedWord N j) :
      (Fin.consEquiv (fun _ : Fin (j+1) => Option (Fin N × Fin N))) (a,w)=Fin.cons a w := rfl
  rw [Fintype.sum_prod_type,Fintype.sum_option]
  simp only [hcons,preferredWordCoefficient,preferredWordMarks,Fin.cons_zero,Fin.tail_cons]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]

/-- Explicit local calculus data for the actual recursively constructed
coefficients. This is strictly weaker than the desired uniform coefficient
bound, and is kept visible in the finite-expansion theorem below. -/
def PreferredWordDifferentiability {N : ℕ} (τ : ℝ) (η p m r : ℝ → ℝ)
    (Ω : Set (ℂ × (Fin N → ℝ))) : Prop :=
  ∀ z∈Ω,
    DifferentiableAt ℂ (fun t => preferredSourceRegularKernel τ p m t z.2) z.1 ∧
    (∀ i, DifferentiableAt ℝ
      (fun x => preferredSourceRegularKernel τ p m z.1 (Function.update z.2 i x)) (z.2 i)) ∧
    ∀ j (w : PreferredMarkedWord N j),
      DifferentiableAt ℂ (fun t => preferredWordCoefficient τ η p m r j w t z.2) z.1 ∧
      (∀ i, DifferentiableAt ℝ
        (fun x => preferredWordCoefficient τ η p m r j w z.1 (Function.update z.2 i x)) (z.2 i))

/-- All finite regular descendants equal their explicit signed-minor sums
on any open source domain carrying the stated actual local calculus data.
No scalar norm estimate or full-tail bound is used in this identity. -/
theorem preferredRegularTransportedScalar_word_expansion {N : ℕ}
    (τ : ℝ) (η p m r : ℝ → ℝ) (Ω : Set (ℂ × (Fin N → ℝ)))
    (hΩ : IsOpen Ω) (hreg : PreferredWordDifferentiability τ η p m r Ω)
    (j : ℕ) (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    preferredRegularTransportedScalar τ η p m r j s θ=preferredWordSum τ η p m r j s θ := by
  classical
  induction j generalizing s θ with
  | zero => exact (preferredWordSum_zero τ η p m r s θ).symm
  | succ j ih =>
    obtain ⟨hKs,hKθ,hA⟩ := hreg (s,θ) hz
    have htermS (w : PreferredMarkedWord N j) : DifferentiableAt ℂ
        (fun t => preferredWordCoefficient τ η p m r j w t θ *
          preferredMarkedMinor (preferredSourceRegularKernel τ p m t θ) (preferredWordMarks j w)) s := by
      apply (hA j w).1.mul
      exact ((preferredMarkedMinor_contDiff (preferredWordMarks j w)).differentiable
        (by simp)).differentiableAt.comp s hKs
    have htermθ (w : PreferredMarkedWord N j) (i : Fin N) : DifferentiableAt ℝ
        (fun x => preferredWordCoefficient τ η p m r j w s (Function.update θ i x) *
          preferredMarkedMinor (preferredSourceRegularKernel τ p m s (Function.update θ i x))
            (preferredWordMarks j w)) (θ i) := by
      apply (hA j w).2 i |>.mul
      have hm := ((preferredMarkedMinor_contDiff (preferredWordMarks j w)).differentiable
        (by simp)).differentiableAt (x := preferredSourceRegularKernel τ p m s (Function.update θ i (θ i)))
      exact ((hm.hasFDerivAt.restrictScalars ℝ).comp (θ i) (hKθ i).hasFDerivAt).differentiableAt
    change preferredRegularTransportStep τ p m
      (preferredRegularTransportedScalar τ η p m r j) s θ = _
    rw [preferredRegularTransportStep_congr_open τ p m _ (preferredWordSum τ η p m r j)
      Ω hΩ (fun z hz => ih z.1 z.2 hz) s θ hz]
    unfold preferredWordSum
    rw [preferredRegularTransportStep_sum τ p m _ s θ htermS htermθ]
    exact (preferredWordSum_succ τ η p m r j s θ
      (fun w => (hA j w).1) (fun w => (hA j w).2) hKs hKθ).symm

end
end IsingBulk.Preferred22
