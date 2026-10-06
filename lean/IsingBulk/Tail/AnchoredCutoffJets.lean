import IsingBulk.Tail.AllBranchExteriorCutoffs

/-! Uniform real coordinate-word jets of the fixed named microcore anchor.
The exact factorized calculation preserves total derivative degree. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets Set
open scoped BigOperators ContDiff

theorem coordinateProduct_word_jet {N : ℕ}
    (g : Fin N → ℕ → ℝ → ℝ)
    (hg : ∀ i k x, HasDerivAt (g i k) (g i (k+1) x) x)
    (l : List (Fin N)) (u : Fin N → ℝ) :
    cutoffJet l (fun x => ∏ i, g i 0 (x i)) u = ∏ i, g i (l.count i) (u i) := by
  induction l generalizing u with
  | nil => simp [cutoffJet]
  | cons q l ih =>
    have he : cutoffJet l (fun x => ∏ i, g i 0 (x i)) =
        (fun x => ∏ i, g i (l.count i) (x i)) := funext ih
    rw [cutoffJet,he]
    dsimp only
    rw [coordinate_product_fderiv _ (fun i x => (hg i (l.count i) x).differentiableAt),
      (hg q (l.count q) (u q)).deriv]
    symm
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ q)]
    congr 1
    · simp only [List.count_cons_self]
    · apply Finset.prod_congr rfl
      intro i hi
      simp only [List.count_cons_of_ne (Finset.ne_of_mem_erase hi).symm]

def anchorCoordinateFactor {N : ℕ} (b : ℝ) (q i : Fin N) (k : ℕ) (u : ℝ) : ℝ :=
  if i<q then scaledCutoffFactor b k u
  else if i=q then (if k=0 then 1-scaledCutoffFactor b 0 u else -scaledCutoffFactor b k u)
  else if k=0 then 1 else 0

theorem anchorCoordinateFactor_hasDerivAt {N : ℕ} (b : ℝ) (q i : Fin N) (k : ℕ) (u : ℝ) :
    HasDerivAt (anchorCoordinateFactor b q i k) (anchorCoordinateFactor b q i (k+1) u) u := by
  change HasDerivAt (fun x => anchorCoordinateFactor b q i k x) (anchorCoordinateFactor b q i (k+1) u) u
  by_cases hi : i<q
  · simpa only [anchorCoordinateFactor,hi,ite_true] using scaledCutoffFactor_hasDerivAt b k u
  · by_cases he : i=q
    · subst i
      by_cases hk : k=0
      · subst k
        simpa only [anchorCoordinateFactor,lt_self_iff_false,ite_false,ite_true,Nat.zero_add,
          Nat.one_ne_zero] using (scaledCutoffFactor_hasDerivAt b 0 u).const_sub 1
      · simpa only [anchorCoordinateFactor,lt_self_iff_false,ite_false,ite_true,hk,
          show k+1 ≠ 0 by omega,zero_sub] using (scaledCutoffFactor_hasDerivAt b k u).const_sub 0
    · simpa only [anchorCoordinateFactor,hi,he,ite_false,show k+1 ≠ 0 by omega] using
        (hasDerivAt_const u (if k=0 then (1:ℝ) else 0))


theorem microExteriorAnchor_coordinate_product {N : ℕ} (b : ℝ) (q : Fin N) (u : Fin N → ℝ) :
    microExteriorAnchor b q u = ∏ i : Fin N, anchorCoordinateFactor b q i 0 (u i) := by
  have hprefix : (∏ i ∈ Finset.univ.filter (fun i : Fin N => i<q), microCutoffBase (u i/b)) =
      ∏ k ∈ Finset.range q, finiteExtension (fun i => microCutoffBase (u i/b)) k := by
    apply Finset.prod_bij (fun i _ => i.val)
    · intro i hi
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
    · intro i hi j hj hij
      exact Fin.ext hij
    · intro k hk
      have hkq := Finset.mem_range.mp hk
      refine ⟨⟨k,hkq.trans q.isLt⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hkq⟩,rfl⟩
    · intro i hi
      exact (finiteExtension_fin (fun i => microCutoffBase (u i/b)) i).symm
  have hf (i : Fin N) : anchorCoordinateFactor b q i 0 (u i) =
      (if i<q then microCutoffBase (u i/b) else 1) *
      (if i=q then 1-microCutoffBase (u q/b) else 1) := by
    by_cases hi : i<q
    · have hn : i≠q := ne_of_lt hi
      simp [anchorCoordinateFactor,hi,hn,scaledCutoffFactor]
    · by_cases he : i=q
      · subst i
        simp [anchorCoordinateFactor,scaledCutoffFactor]
      · simp [anchorCoordinateFactor,hi,he]
  simp_rw [hf]
  rw [Finset.prod_mul_distrib]
  have hn : (∏ i : Fin N, if i=q then 1-microCutoffBase (u q/b) else 1)=1-microCutoffBase (u q/b) := by simp
  rw [hn]
  have hp : (∏ i : Fin N, if i<q then microCutoffBase (u i/b) else 1)=
      ∏ i ∈ Finset.univ.filter (fun i : Fin N => i<q), microCutoffBase (u i/b) := by
    rw [Finset.prod_ite]
    simp
  rw [hp,hprefix]
  unfold microExteriorAnchor outerAnchor
  rw [finiteExtension_fin]
  ring

theorem microExteriorAnchor_word_jet {N : ℕ} (b : ℝ) (q : Fin N)
    (l : List (Fin N)) (u : Fin N → ℝ) :
    cutoffJet l (microExteriorAnchor b q) u = ∏ i, anchorCoordinateFactor b q i (l.count i) (u i) := by
  have he : microExteriorAnchor b q = fun x => ∏ i, anchorCoordinateFactor b q i 0 (x i) :=
    funext (microExteriorAnchor_coordinate_product b q)
  rw [he]
  exact coordinateProduct_word_jet _ (anchorCoordinateFactor_hasDerivAt b q) l u


theorem microExteriorAnchor_jet_bound (j : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ N : ℕ, ∀ b : ℝ, 0 < b → b ≤ 1 →
      ∀ q : Fin N, ∀ l : List (Fin N), l.length ≤ j → ∀ u : Fin N → ℝ,
        ‖cutoffJet l (microExteriorAnchor b q) u‖ ≤ C^N*(b⁻¹)^j := by
  obtain ⟨C,hC,hder⟩ := microCutoffBase_derivatives_bounded j
  refine ⟨C,hC,?_⟩
  intro N b hb hb1 q l hl u
  have hscaled (k : ℕ) (hk : k≤j) (x : ℝ) :
      ‖scaledCutoffFactor b k x‖ ≤ (b⁻¹)^k*C := by
    rw [scaledCutoffFactor,norm_mul,norm_pow,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hb)]
    exact mul_le_mul_of_nonneg_left (hder k hk _) (by positivity)
  have hf (i : Fin N) : ‖anchorCoordinateFactor b q i (l.count i) (u i)‖ ≤ (b⁻¹)^(l.count i)*C := by
    have hk : l.count i≤j := List.count_le_length.trans hl
    unfold anchorCoordinateFactor
    split_ifs with hi he hz
    · exact hscaled _ hk _
    · rw [hz]
      simp only [scaledCutoffFactor,pow_zero,iteratedDeriv_zero,one_mul]
      have h0 : 0 ≤ microCutoffBase (u i/b) := (fixedBranchBump 1 (by norm_num)).nonneg
      have h1 : microCutoffBase (u i/b) ≤ 1 := (fixedBranchBump 1 (by norm_num)).le_one
      rw [Real.norm_eq_abs,abs_of_nonneg (by linarith)]
      linarith
    · simpa only [norm_neg] using hscaled _ hk (u i)
    · simp only [norm_one]
      have hp : 1 ≤ (b⁻¹)^(l.count i) := one_le_pow₀ ((one_le_inv₀ hb).mpr hb1)
      nlinarith
    · simp only [norm_zero]
      positivity
  rw [microExteriorAnchor_word_jet,norm_prod]
  calc
    _ ≤ ∏ i : Fin N, (b⁻¹)^(l.count i)*C :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hf i)
    _ = C^N*(b⁻¹)^l.length := by
      rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,list_sum_coordinate_counts]
      simp [mul_comm]
    _ ≤ C^N*(b⁻¹)^j := mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ ((one_le_inv₀ hb).mpr hb1) hl) (by positivity)

end
end IsingBulk.Tail
