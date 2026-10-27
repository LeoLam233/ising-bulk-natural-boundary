import IsingBulk.Preferred22.MarkedMinorNormalization

/-! Quantitative mixed determinant jets obtained from genuine marked minors.
The unmarked small-kernel power is retained, with only fixed-order polynomial
loss in N. The hypotheses concern actual kernel derivatives, never a minor or
complete-tail bound. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

theorem norm_determinant_jet_le_marked {N ell : ℕ} (hN : 0<N)
    (K : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ha : 0<a)
    (hK : ∀ i j, ‖K i j‖ ≤ a) :
    ‖iteratedFDeriv ℂ ell Matrix.det K‖ ≤
      (N:ℝ)^(2*ell)*(Real.sqrt N)^N*a^(N-ell) := by
  classical
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro B
  rw [determinant_jet_marked_expansion]
  calc
    _ ≤ ∑ marks : Fin ell → Fin N × Fin N,
        ‖(∏ r, B r (marks r).1 (marks r).2)*markedDeterminant K marks‖ := norm_sum_le _ _
    _ ≤ ∑ _marks : Fin ell → Fin N × Fin N,
        (∏ r, ‖B r‖)*((Real.sqrt N)^N*a^(N-ell)) := by
      apply Finset.sum_le_sum
      intro marks _
      rw [norm_mul, norm_prod]
      apply mul_le_mul
      · exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
          (fun r _ => Matrix.norm_entry_le_entrywise_sup_norm (B r))
      · exact markedDeterminant_hadamard hN K marks a ha hK
      · exact norm_nonneg _
      · positivity
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, marked_entry_index_card, nsmul_eq_mul,
        Nat.cast_pow]
      ring

theorem composite_determinant_jet_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {N k : ℕ} (hN : 0<N) (K : E → Matrix (Fin N) (Fin N) ℂ) (x : E)
    (hK : ContDiffAt ℂ ∞ K x) (a C : ℝ) (ha : 0<a) (ha1 : a≤1) (hC : 1≤C)
    (hentry : ∀ i j, ‖K x i j‖≤a)
    (hjet : ∀ r : ℕ, 0<r → r≤k → ‖iteratedFDeriv ℂ r K x‖≤C) :
    ‖iteratedFDeriv ℂ k (fun y => (K y).det) x‖ ≤
      (Fintype.card (OrderedFinpartition k):ℝ)*(N:ℝ)^(2*k)*C^k*
        (Real.sqrt N)^N*a^(N-k) := by
  classical
  change ‖iteratedFDeriv ℂ k (Matrix.det ∘ K) x‖ ≤ _
  rw [iteratedFDeriv_comp (determinant_contDiff N).contDiffAt hK (by simp)]
  simp only [FormalMultilinearSeries.taylorComp]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _c : OrderedFinpartition k,
        (N:ℝ)^(2*k)*C^k*(Real.sqrt N)^N*a^(N-k) := by
      apply Finset.sum_le_sum
      intro c _
      have hinner : (∏ r : Fin c.length, ‖iteratedFDeriv ℂ (c.partSize r) K x‖) ≤ C^c.length := by
        simpa using Finset.prod_le_prod₀ (s := (Finset.univ : Finset (Fin c.length)))
          (fun _ _ => norm_nonneg _)
          (fun r _ => hjet _ (c.partSize_pos r) (c.partSize_le r))
      have houter := norm_determinant_jet_le_marked (ell := c.length) hN (K x) a ha hentry
      have hd := c.norm_compAlongOrderedFinpartition_le
        (iteratedFDeriv ℂ c.length Matrix.det (K x))
        (fun r => iteratedFDeriv ℂ (c.partSize r) K x)
      have hN1 : (1:ℝ)≤N := by exact_mod_cast hN
      have hn : (N:ℝ)^(2*c.length)≤(N:ℝ)^(2*k) :=
        pow_le_pow_right₀ hN1 (Nat.mul_le_mul_left 2 c.length_le)
      have hc : C^c.length≤C^k := pow_le_pow_right₀ hC c.length_le
      have hsmall : a^(N-c.length)≤a^(N-k) :=
        pow_le_pow_of_le_one ha.le ha1 (Nat.sub_le_sub_left c.length_le N)
      apply hd.trans
      calc
        _ ≤ ((N:ℝ)^(2*c.length)*(Real.sqrt N)^N*a^(N-c.length))*C^c.length :=
          mul_le_mul houter hinner (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) (by positivity)
        _ ≤ ((N:ℝ)^(2*k)*(Real.sqrt N)^N*a^(N-k))*C^k := by gcongr
        _ = _ := by ring
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

theorem composite_determinant_jet_factorial_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {N k : ℕ} (hN : 0<N) (K : E → Matrix (Fin N) (Fin N) ℂ) (x : E)
    (hK : ContDiffAt ℂ ∞ K x) (a C : ℝ) (ha : 0<a) (ha1 : a≤1) (hC : 1≤C)
    (hentry : ∀ i j, ‖K x i j‖≤a)
    (hjet : ∀ r : ℕ, 0<r → r≤k → ‖iteratedFDeriv ℂ r K x‖≤C) :
    ‖iteratedFDeriv ℂ k (fun y => (K y).det) x‖/(N.factorial:ℝ) ≤
      (Fintype.card (OrderedFinpartition k):ℝ)*(N:ℝ)^(2*k)*C^k*
        (Real.exp 1/Real.sqrt N)^N*a^(N-k) := by
  have hf : (0:ℝ)≤N.factorial := Nat.cast_nonneg _
  have he : (Real.sqrt N)^N/(N.factorial:ℝ) ≤ (Real.exp 1/Real.sqrt N)^N := by
    simpa only [mul_one] using sqrt_factorial_envelope hN (B := 1) (by norm_num)
  calc
    _ ≤ ((Fintype.card (OrderedFinpartition k):ℝ)*(N:ℝ)^(2*k)*C^k*
        (Real.sqrt N)^N*a^(N-k))/(N.factorial:ℝ) :=
      div_le_div_of_nonneg_right (composite_determinant_jet_bound hN K x hK a C ha ha1 hC hentry hjet) hf
    _ = ((Fintype.card (OrderedFinpartition k):ℝ)*(N:ℝ)^(2*k)*C^k*a^(N-k))*
        ((Real.sqrt N)^N/(N.factorial:ℝ)) := by ring
    _ ≤ ((Fintype.card (OrderedFinpartition k):ℝ)*(N:ℝ)^(2*k)*C^k*a^(N-k))*
        (Real.exp 1/Real.sqrt N)^N := mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by ring

end
end IsingBulk.Preferred22
