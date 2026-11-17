import IsingBulk.AnisoF002.C03.IsotropicRightCutoff

/-!
# Full right cutoff products and exact compact-anchor telescoping

There is one term per named angle.  All real jets of each product and
anchor term have a single fixed-order exponential-in-N bound, before
any particle number is selected.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter
open scoped Topology BigOperators Classical

theorem finiteJetControl_finsetProd {E ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [DecidableEq ι] (u : Finset ι) (k : ℕ)
    (f : ι → E → ℂ) {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ i ∈ u, FiniteJetControl k (f i) L) :
    FiniteJetControl k (fun x => ∏ i ∈ u, f i x) ((2 ^ k * L) ^ u.card) := by
  revert hf
  induction u using Finset.induction_on with
  | empty =>
    intro _
    simpa only [Finset.prod_empty, Finset.card_empty, pow_zero] using
      finiteJetControl_const (E := E) k (1 : ℂ) 1 (by simp)
  | @insert a u ha ih =>
    intro hf
    have hfa := hf a (Finset.mem_insert_self _ _)
    have hfu := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have hm := hfa.mul hfu hL (pow_nonneg (mul_nonneg (by positivity) hL) _)
    have he : (fun x => ∏ i ∈ insert a u, f i x) = fun x => f a x * ∏ i ∈ u, f i x := by
      funext x
      rw [Finset.prod_insert ha]
    rw [he]
    apply hm.mono_bound
    rw [Finset.card_insert_of_notMem ha, pow_succ]
    exact le_of_eq (by ring)

def rightCutoffProduct (b δ ρ : ℝ) (N : ℕ) (θ : Fin N → ℝ) : ℂ :=
  ∏ i, (periodicRightCutoff b δ ρ (θ i) : ℂ)

def rightCutoffAnchor (b δ ρ : ℝ) {N : ℕ} (a : Fin N) (θ : Fin N → ℝ) : ℂ :=
  (1 - (periodicRightCutoff b δ ρ (θ a) : ℂ)) *
    ∏ i ∈ Finset.univ.filter (fun i : Fin N => i < a), (periodicRightCutoff b δ ρ (θ i) : ℂ)

theorem rightCutoff_coordinate_contDiff (b δ ρ : ℝ) {N : ℕ} (i : Fin N) {k : ℕ∞} :
    ContDiff ℝ k (fun θ : Fin N → ℝ => (periodicRightCutoff b δ ρ (θ i) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp ((periodicRightCutoff_contDiff b δ ρ).comp (contDiff_apply ℝ ℝ i))

theorem rightCutoffProduct_contDiff (b δ ρ : ℝ) (N : ℕ) {k : ℕ∞} :
    ContDiff ℝ k (rightCutoffProduct b δ ρ N) :=
  contDiff_prod (fun i _ => rightCutoff_coordinate_contDiff b δ ρ i)

theorem rightCutoffAnchor_contDiff (b δ ρ : ℝ) {N : ℕ} (a : Fin N) {k : ℕ∞} :
    ContDiff ℝ k (rightCutoffAnchor b δ ρ a) :=
  (contDiff_const.sub (rightCutoff_coordinate_contDiff b δ ρ a)).mul
    (contDiff_prod (fun i _ => rightCutoff_coordinate_contDiff b δ ρ i))

theorem rightCutoffAnchor_as_product (b δ ρ : ℝ) {N : ℕ} (a : Fin N) :
    rightCutoffAnchor b δ ρ a = fun θ : Fin N → ℝ =>
      ∏ i ∈ insert a (Finset.univ.filter (fun i : Fin N => i < a)),
        if i = a then 1 - (periodicRightCutoff b δ ρ (θ i) : ℂ)
        else (periodicRightCutoff b δ ρ (θ i) : ℂ) := by
  funext θ
  have ha : a ∉ Finset.univ.filter (fun i : Fin N => i < a) := by simp
  rw [Finset.prod_insert ha]
  simp only [↓reduceIte]
  unfold rightCutoffAnchor
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hia : i ≠ a := ne_of_lt (Finset.mem_filter.mp hi).2
  simp only [hia, ↓reduceIte]

theorem rightCutoff_exact_telescope (b δ ρ : ℝ) (N : ℕ) (θ : Fin N → ℝ) :
    1 - rightCutoffProduct b δ ρ N θ = ∑ a, rightCutoffAnchor b δ ρ a θ := by
  have he := Finset.prod_one_sub_ordered (R := ℂ) (Finset.univ : Finset (Fin N))
    (fun i => 1 - (periodicRightCutoff b δ ρ (θ i) : ℂ))
  simp only [sub_sub_cancel] at he
  change rightCutoffProduct b δ ρ N θ = 1 - ∑ a, rightCutoffAnchor b δ ρ a θ at he
  linear_combination -he

theorem rightCutoff_exact_partition (b δ ρ : ℝ) (N : ℕ) (θ : Fin N → ℝ) :
    (1 : ℂ) = rightCutoffProduct b δ ρ N θ + ∑ a, rightCutoffAnchor b δ ρ a θ := by
  linear_combination rightCutoff_exact_telescope b δ ρ N θ

theorem exists_rightCutoff_product_anchor_jets (b δ ρ : ℝ) (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ N : ℕ,
      FiniteJetControl k (rightCutoffProduct b δ ρ N) (C ^ N) ∧
      ∀ a : Fin N, FiniteJetControl k (rightCutoffAnchor b δ ρ a) (C ^ N) := by
  obtain ⟨L, hL, hjet⟩ := periodicRightCutoff_scalar_jets b δ ρ k
  let C := 2 ^ k * (L + 1)
  have hLp : 0 ≤ L := by linarith
  have hL1 : 0 ≤ L + 1 := by linarith
  have hC : 1 ≤ C := one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) (by linarith)
  refine ⟨C, hC, ?_⟩
  intro N
  have hcoord (i : Fin N) : FiniteJetControl k
      (fun θ : Fin N → ℝ => (periodicRightCutoff b δ ρ (θ i) : ℂ)) L :=
    finiteJetControl_complex_coordinate hjet i
  constructor
  · have hp := finiteJetControl_finsetProd (Finset.univ : Finset (Fin N)) k
      (fun i (θ : Fin N → ℝ) => (periodicRightCutoff b δ ρ (θ i) : ℂ)) hL1
      (fun i _ => (hcoord i).mono_bound (by linarith))
    change FiniteJetControl k
      (fun θ : Fin N → ℝ => ∏ i, (periodicRightCutoff b δ ρ (θ i) : ℂ))
      ((2 ^ k * (L + 1)) ^ N)
    simpa only [Finset.card_univ, Fintype.card_fin] using hp
  · intro a
    let S := insert a (Finset.univ.filter (fun i : Fin N => i < a))
    let f : Fin N → (Fin N → ℝ) → ℂ := fun i θ =>
      if i = a then 1 - (periodicRightCutoff b δ ρ (θ i) : ℂ)
      else (periodicRightCutoff b δ ρ (θ i) : ℂ)
    have hf (i : Fin N) : FiniteJetControl k (f i) (L + 1) := by
      by_cases hi : i = a
      · subst i
        dsimp only [f, ↓reduceIte]
        have hh : FiniteJetControl k
            (fun θ : Fin N → ℝ => (1 : ℂ) - (periodicRightCutoff b δ ρ (θ a) : ℂ))
            (1 + L) :=
          (finiteJetControl_const (E := Fin N → ℝ) k (1 : ℂ) 1 (by simp)).sub (hcoord a)
        simpa only [add_comm, ite_true] using hh
      · dsimp only [f]
        simp only [hi, ↓reduceIte]
        exact (hcoord i).mono_bound (by linarith)
    have hp := finiteJetControl_finsetProd S k f hL1 (fun i _ => hf i)
    have hcard : S.card ≤ N := by
      simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_le_card (Finset.subset_univ S)
    rw [rightCutoffAnchor_as_product]
    exact hp.mono_bound (pow_le_pow_right₀ hC hcard)

theorem rightCutoffProduct_norm_le_one (b δ ρ : ℝ) (N : ℕ) (θ : Fin N → ℝ) :
    ‖rightCutoffProduct b δ ρ N θ‖ ≤ 1 := by
  unfold rightCutoffProduct
  rw [norm_prod]
  apply Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => ?_)
  rw [Complex.norm_real, Real.norm_of_nonneg (periodicRightCutoff_bounds b δ ρ (θ i)).1]
  exact (periodicRightCutoff_bounds b δ ρ (θ i)).2

end
end IsingBulk.AnisoF002.Isotropic
