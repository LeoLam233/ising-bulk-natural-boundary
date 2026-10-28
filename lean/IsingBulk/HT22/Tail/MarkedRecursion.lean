import IsingBulk.HT22.Tail.MarkedTransport
import IsingBulk.Preferred22.MarkedTransportRecursion

/-! # Actual all-order ordinary-marked recurrence

The finite word/count combinatorics are reused, while every coefficient is
computed by the fixed-v mixed-covariance HT22 operator and every minor is
an actual constant-bordered odd-kernel minor. No descendant bounds are
assumed by this identity.
-/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 Filter
open scoped BigOperators ContDiff Matrix.Norms.Elementwise Topology
set_option backward.isDefEq.respectTransparency false

def ordinaryMarkedMinor {N : ℕ} (K : Matrix (Fin N) (Fin N) ℂ)
    (marks : List (Fin N × Fin N)) : ℂ := Algebra.borderedMarkedDeterminant K marks.get

theorem ordinaryMarkedMinor_cons_eq {N : ℕ} (K : Matrix (Fin N) (Fin N) ℂ)
    (a : Fin N × Fin N) (marks : List (Fin N × Fin N)) :
    ordinaryMarkedMinor K (a::marks)=Algebra.borderedMarkedDeterminant K (Fin.cons a marks.get) := by
  rfl

theorem ordinaryMarkedMinor_contDiff {N : ℕ} (marks : List (Fin N × Fin N)) :
    ContDiff ℂ ∞ (fun K : Matrix (Fin N) (Fin N) ℂ => ordinaryMarkedMinor K marks) := by
  have hg : ContDiff ℂ ∞ (fun K : Matrix (Fin N) (Fin N) ℂ => Algebra.ghostBorder K (fun _ => 1)) := by
    have he : (fun K : Matrix (Fin N) (Fin N) ℂ => Algebra.ghostBorder K (fun _ => 1))=
        (fun K => Algebra.ordinaryDirectionCLM N K+Algebra.ghostBorder 0 (fun _ => 1)) :=
      funext Algebra.ghostBorder_eq_affine
    rw [he]
    exact (Algebra.ordinaryDirectionCLM N).contDiff.add contDiff_const
  exact (markedDeterminant_contDiff (Algebra.ordinaryMarks marks.get)).comp hg

theorem regularTransportStep_list_marked {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (A : ℂ → (Fin N → ℝ) → ℂ) (s : ℂ) (θ : Fin N → ℝ)
    (marks : List (Fin N × Fin N))
    (hAs : DifferentiableAt ℂ (fun t => A t θ) s)
    (hAθ : ∀ i, DifferentiableAt ℝ (fun x => A s (Function.update θ i x)) (θ i))
    (hKs : DifferentiableAt ℂ (fun t => sourceOrdinaryKernel τ p m t θ) s)
    (hKθ : ∀ i, DifferentiableAt ℝ
      (fun x => sourceOrdinaryKernel τ p m s (Function.update θ i x)) (θ i)) :
    regularTransportStep τ p m
      (fun t x => A t x*ordinaryMarkedMinor (sourceOrdinaryKernel τ p m t x) marks) s θ =
      regularTransportStep τ p m A s θ*ordinaryMarkedMinor (sourceOrdinaryKernel τ p m s θ) marks +
      ∑ a : Fin N × Fin N, (A s θ*ordinaryMaterialEntry τ p m s θ a)*
        ordinaryMarkedMinor (sourceOrdinaryKernel τ p m s θ) (a::marks) := by
  simp_rw [ordinaryMarkedMinor_cons_eq]
  exact regularTransportStep_ordinary_marked τ p m A s θ marks.get hAs hAθ hKs hKθ

theorem regularSeed_eq_empty_minor {N : ℕ} (τ : ℝ) (η p m r : ℝ → ℝ)
    (s : ℂ) (θ : Fin N → ℝ) :
    regularSeed τ η p m r s θ=regularSeedCoefficient τ η p m r s θ*
      ordinaryMarkedMinor (sourceOrdinaryKernel τ p m s θ) [] := by
  simp only [ordinaryMarkedMinor,Algebra.borderedMarkedDeterminant,markedDeterminant,
    List.length_nil,iteratedFDeriv_zero_apply]
  rfl

abbrev MarkedWord := PreferredMarkedWord
abbrev wordMarks := @preferredWordMarks
abbrev wordLoss := @preferredWordLoss

def wordCoefficient {N : ℕ} (τ : ℝ) (η p m r : ℝ → ℝ) :
    (j : ℕ) → MarkedWord N j → ℂ → (Fin N → ℝ) → ℂ
  | 0, _ => regularSeedCoefficient τ η p m r
  | j+1, w => match w 0 with
    | none => regularTransportStep τ p m
        (wordCoefficient τ η p m r j (Fin.tail w))
    | some a => fun s θ => wordCoefficient τ η p m r j (Fin.tail w) s θ *
        ordinaryMaterialEntry τ p m s θ a

def wordSum {N : ℕ} (τ : ℝ) (η p m r : ℝ → ℝ)
    (j : ℕ) (s : ℂ) (θ : Fin N → ℝ) : ℂ :=
  ∑ w : MarkedWord N j, wordCoefficient τ η p m r j w s θ *
    ordinaryMarkedMinor (sourceOrdinaryKernel τ p m s θ) (wordMarks j w)

theorem wordSum_zero {N : ℕ} (τ : ℝ) (η p m r : ℝ → ℝ)
    (s : ℂ) (θ : Fin N → ℝ) : wordSum τ η p m r 0 s θ=regularSeed τ η p m r s θ := by
  rw [regularSeed_eq_empty_minor]
  simp [wordSum,wordCoefficient,wordMarks,preferredWordMarks]

/-- The actual generator is local in the product of the parameter and real
angular variables; no analyticity is needed to transport germ equalities. -/
theorem regularTransportStep_congr_open {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (A G : ℂ → (Fin N → ℝ) → ℂ) (Ω : Set (ℂ × (Fin N → ℝ)))
    (hΩ : IsOpen Ω) (hEq : ∀ z ∈ Ω, A z.1 z.2=G z.1 z.2)
    (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    regularTransportStep τ p m A s θ=regularTransportStep τ p m G s θ := by
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
  rw [regularTransportStep_eq,regularTransportStep_eq,hs,hEq (s,θ) hz]
  simp_rw [hx]

theorem regularTransportStep_sum {N : ℕ} {ι : Type*} [Fintype ι]
    (τ : ℝ) (p m : ℝ → ℝ) (F : ι → ℂ → (Fin N → ℝ) → ℂ)
    (s : ℂ) (θ : Fin N → ℝ)
    (hs : ∀ a, DifferentiableAt ℂ (fun t => F a t θ) s)
    (hθ : ∀ a i, DifferentiableAt ℝ (fun x => F a s (Function.update θ i x)) (θ i)) :
    regularTransportStep τ p m (fun t x => ∑ a, F a t x) s θ =
      ∑ a, regularTransportStep τ p m (F a) s θ := by
  classical
  simp_rw [regularTransportStep_eq]
  rw [deriv_fun_sum (fun a _ => hs a)]
  simp_rw [deriv_fun_sum (fun a _ => hθ a _)]
  simp only [Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_comm]

theorem wordSum_succ {N : ℕ} (τ : ℝ) (η p m r : ℝ → ℝ)
    (j : ℕ) (s : ℂ) (θ : Fin N → ℝ)
    (hAs : ∀ w : MarkedWord N j,
      DifferentiableAt ℂ (fun t => wordCoefficient τ η p m r j w t θ) s)
    (hAθ : ∀ (w : MarkedWord N j) i, DifferentiableAt ℝ
      (fun x => wordCoefficient τ η p m r j w s (Function.update θ i x)) (θ i))
    (hKs : DifferentiableAt ℂ (fun t => sourceOrdinaryKernel τ p m t θ) s)
    (hKθ : ∀ i, DifferentiableAt ℝ
      (fun x => sourceOrdinaryKernel τ p m s (Function.update θ i x)) (θ i)) :
    wordSum τ η p m r (j+1) s θ =
      ∑ w : MarkedWord N j, regularTransportStep τ p m
        (fun t x => wordCoefficient τ η p m r j w t x *
          ordinaryMarkedMinor (sourceOrdinaryKernel τ p m t x) (wordMarks j w)) s θ := by
  classical
  simp_rw [regularTransportStep_list_marked τ p m _ s θ _ (hAs _) (hAθ _) hKs hKθ]
  unfold wordSum
  rw [← (Fin.consEquiv (fun _ : Fin (j+1) => Option (Fin N × Fin N))).sum_comp]
  have hcons (a : Option (Fin N × Fin N)) (w : MarkedWord N j) :
      (Fin.consEquiv (fun _ : Fin (j+1) => Option (Fin N × Fin N))) (a,w)=Fin.cons a w := rfl
  rw [Fintype.sum_prod_type,Fintype.sum_option]
  simp only [hcons,wordCoefficient,wordMarks,preferredWordMarks,Fin.cons_zero,Fin.tail_cons]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]

/-- Explicit local calculus data for the actual recursively constructed
coefficients. This is strictly weaker than the desired uniform coefficient
bound, and is kept visible in the finite-expansion theorem below. -/
def WordDifferentiability {N : ℕ} (τ : ℝ) (η p m r : ℝ → ℝ)
    (Ω : Set (ℂ × (Fin N → ℝ))) : Prop :=
  ∀ z∈Ω,
    DifferentiableAt ℂ (fun t => sourceOrdinaryKernel τ p m t z.2) z.1 ∧
    (∀ i, DifferentiableAt ℝ
      (fun x => sourceOrdinaryKernel τ p m z.1 (Function.update z.2 i x)) (z.2 i)) ∧
    ∀ j (w : MarkedWord N j),
      DifferentiableAt ℂ (fun t => wordCoefficient τ η p m r j w t z.2) z.1 ∧
      (∀ i, DifferentiableAt ℝ
        (fun x => wordCoefficient τ η p m r j w z.1 (Function.update z.2 i x)) (z.2 i))

/-- All finite regular descendants equal their explicit signed-minor sums
on any open source domain carrying the stated actual local calculus data.
No scalar norm estimate or full-tail bound is used in this identity. -/
theorem regularTransportedScalar_word_expansion {N : ℕ}
    (τ : ℝ) (η p m r : ℝ → ℝ) (Ω : Set (ℂ × (Fin N → ℝ)))
    (hΩ : IsOpen Ω) (hreg : WordDifferentiability τ η p m r Ω)
    (j : ℕ) (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    regularTransportedScalar τ η p m r j s θ=wordSum τ η p m r j s θ := by
  classical
  induction j generalizing s θ with
  | zero => exact (wordSum_zero τ η p m r s θ).symm
  | succ j ih =>
    obtain ⟨hKs,hKθ,hA⟩ := hreg (s,θ) hz
    have htermS (w : MarkedWord N j) : DifferentiableAt ℂ
        (fun t => wordCoefficient τ η p m r j w t θ *
          ordinaryMarkedMinor (sourceOrdinaryKernel τ p m t θ) (wordMarks j w)) s := by
      apply (hA j w).1.mul
      exact ((ordinaryMarkedMinor_contDiff (wordMarks j w)).differentiable
        (by simp)).differentiableAt.comp s hKs
    have htermθ (w : MarkedWord N j) (i : Fin N) : DifferentiableAt ℝ
        (fun x => wordCoefficient τ η p m r j w s (Function.update θ i x) *
          ordinaryMarkedMinor (sourceOrdinaryKernel τ p m s (Function.update θ i x))
            (wordMarks j w)) (θ i) := by
      apply (hA j w).2 i |>.mul
      have hm := ((ordinaryMarkedMinor_contDiff (wordMarks j w)).differentiable
        (by simp)).differentiableAt (x := sourceOrdinaryKernel τ p m s (Function.update θ i (θ i)))
      exact ((hm.hasFDerivAt.restrictScalars ℝ).comp (θ i) (hKθ i).hasFDerivAt).differentiableAt
    change regularTransportStep τ p m
      (regularTransportedScalar τ η p m r j) s θ = _
    rw [regularTransportStep_congr_open τ p m _ (wordSum τ η p m r j)
      Ω hΩ (fun z hz => ih z.1 z.2 hz) s θ hz]
    unfold wordSum
    rw [regularTransportStep_sum τ p m _ s θ htermS htermθ]
    exact (wordSum_succ τ η p m r j s θ
      (fun w => (hA j w).1) (fun w => (hA j w).2) hKs hKθ).symm

end
end IsingBulk.HT22.Tail
