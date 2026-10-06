import IsingBulk.Tail.ActualCompactGuardedValues
import IsingBulk.Tail.CollisionScaleSummability
import IsingBulk.Tail.GaussianEnvelopeSummability

namespace IsingBulk.Tail
noncomputable section
open Filter

theorem NatExponentialEnvelope.comp_succ {k : ℕ} {f : ℕ → ℝ}
    (hf : NatExponentialEnvelope k f) : NatExponentialEnvelope k (fun N => f (N+1)) := by
  obtain ⟨C,hC,hf⟩ := hf
  refine ⟨C*2^k,by positivity,?_⟩
  intro N hN
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  apply (hf (N+1) (by omega)).trans
  apply Real.exp_le_exp.mpr
  have hp := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ N+1) (by linarith : (N:ℝ)+1 ≤ 2*N) k
  push_cast
  calc
    C*((N:ℝ)+1)^k ≤ C*(2*N)^k := mul_le_mul_of_nonneg_left hp hC
    _ = _ := by rw [mul_pow]; ring

theorem NatExponentialEnvelope.max_one {k : ℕ} {f : ℕ → ℝ}
    (hf : NatExponentialEnvelope k f) (hpos : ∀ N, 0 ≤ f N) :
    NatExponentialEnvelope k (fun N => max 1 (f N)) := by
  apply ((NatExponentialEnvelope.const k 1).add hf).mono_abs
  intro N _
  rw [abs_of_nonneg (zero_le_one.trans (le_max_left _ _)),abs_of_nonneg (by linarith [hpos N])]
  exact max_le (by linarith [hpos N]) (by linarith)

theorem compactGuardedLieCost_envelope (M J : ℕ) (K G T : ℝ) :
    NatExponentialEnvelope 1 (fun N => compactGuardedLieCost N M J K G T) := by
  have hc : NatExponentialEnvelope 1 (fun N => compactPairWeightJetConstant N M J) := by
    unfold compactPairWeightJetConstant
    exact (NatExponentialEnvelope.const 1 ((2:ℝ)^J*(2^(2*M)*(2*M:ℕ)^J))).mul
      ((NatExponentialEnvelope.const 1 ((J.factorial:ℝ)^2)).mul
        ((((NatExponentialEnvelope.id.pow 2).mul
          (NatExponentialEnvelope.const 1 ((2:ℝ)^(2*M)*(2*M:ℕ)^J))).max_one (fun _ => by positivity)).pow J))
  unfold compactGuardedLieCost
  exact (((NatExponentialEnvelope.const 1 ((2:ℝ)^(2*J)*T^(2*M))).mul hc).mul
    (NatExponentialEnvelope.const 1 G)).mul
    (((NatExponentialEnvelope.const 1 1).add
      ((NatExponentialEnvelope.id.mul (NatExponentialEnvelope.const 1 ((2:ℝ)^J))).mul
        ((NatExponentialEnvelope.const 1 K).mul (NatExponentialEnvelope.id.pow (2*(J+2)))))).pow J)

theorem compact_collision_numerator_envelope (J : ℕ) (C : ℝ) :
    NatExponentialEnvelope 2 (fun N => 2^(3*J)*C^(2*N^2+2*N)*(N:ℝ)^(8*J)) := by
  have hq := NatExponentialEnvelope.const_pow (k := 2) (C^2) (fun N => N^2) (fun _ _ => le_rfl)
  have hl := NatExponentialEnvelope.const_pow (k := 2) (C^2) (fun N => N) (fun N hN => by nlinarith)
  have hh := ((NatExponentialEnvelope.const 2 ((2:ℝ)^(3*J))).mul (hq.mul hl)).mul
    ((NatExponentialEnvelope.id.pow (8*J)).mono_degree (by omega : 1 ≤ 2))
  convert hh using 1
  funext N
  simp only [pow_add,pow_mul]

/-- A linear exponential coefficient does not defeat quadratic Gaussian decay. -/
theorem compact_linear_gaussian_summable {f : ℕ → ℝ}
    (hf : NatExponentialEnvelope 1 f) {κ : ℝ} (hκ : 0 < κ) :
    Summable (fun N => f N*Real.exp (-κ*(N:ℝ)^2)) := by
  obtain ⟨C,hC,hf⟩ := hf
  apply (summable_polynomial_gaussian C hκ 0).of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
  rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (C*N)*Real.exp (-κ*(N:ℝ)^2) :=
      mul_le_mul_of_nonneg_right (by simpa only [pow_one] using hf N hN) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; simp only [pow_zero,one_mul,sub_eq_add_neg,neg_mul]

/-- The same exponential near scale works for a pair set omitting one current
coordinate. Its quadratic collision degree beats every quadratic prefactor. -/
theorem compact_deleted_collision_summable {f : ℕ → ℝ}
    (hf : NatExponentialEnvelope 2 f) (m : ℕ) :
    ∃ B₀ : ℝ, 0 < B₀ ∧ ∀ B : ℝ, B₀ ≤ B →
      Summable (fun N : ℕ => f N*(Real.exp (-B*(N:ℝ)))^((N-1)*(N-2)-m)) := by
  obtain ⟨B₀,hB₀,hmain⟩ := collision_scale_summable hf.comp_succ (NatExponentialEnvelope.const 1 1) m
  refine ⟨B₀,hB₀,?_⟩
  intro B hB
  have hBp : 0 < B := hB₀.trans_le hB
  apply (summable_nat_add_iff 1).mp
  apply (hmain B hB).norm.of_norm_bounded
  intro N
  have he : (N+1-1)*(N+1-2)-m=N*(N-1)-m := by
    rw [show N+1-1=N by omega,show N+1-2=N-1 by omega]
  simp only [he,one_pow,mul_one,Real.norm_eq_abs,abs_mul,abs_pow,
    abs_of_pos (Real.exp_pos _),abs_of_pos (by positivity : 0 < 4*Real.exp (-B*(N:ℝ)))]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply pow_le_pow_left₀ (Real.exp_nonneg _)
  calc
    Real.exp (-B*(N+1:ℕ)) ≤ Real.exp (-B*(N:ℝ)) := Real.exp_le_exp.mpr (by push_cast; nlinarith)
    _ ≤ 4*Real.exp (-B*(N:ℝ)) := by linarith [Real.exp_pos (-B*(N:ℝ))]

theorem compact_near_far_summable {near far : ℕ → ℝ}
    (hn : NatExponentialEnvelope 2 near) (hf : NatExponentialEnvelope 1 far)
    (m q : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ B₀ : ℝ, 0 < B₀ ∧ ∀ B : ℝ, B₀ ≤ B →
      Summable (fun N : ℕ =>
        near N*(Real.exp (-B*(N:ℝ)))^((N-1)*(N-2)-m)+
        far N*(Real.exp (-B*(N:ℝ)))^(-(q:ℤ))*Real.exp (-κ*(N:ℝ)^2)) := by
  obtain ⟨B₀,hB₀,hnB⟩ := compact_deleted_collision_summable hn m
  refine ⟨B₀,hB₀,?_⟩
  intro B hB
  have he : NatExponentialEnvelope 1 (fun N : ℕ => (Real.exp (-B*(N:ℝ)))^(-(q:ℤ))) := by
    simpa only [zpow_neg,zpow_natCast,← inv_pow,← Real.exp_neg,neg_mul,neg_neg,pow_one] using
      (NatExponentialEnvelope.exp_monomial 1 B).pow q
  exact (hnB B hB).add (compact_linear_gaussian_summable (hf.mul he) hκ)

end
end IsingBulk.Tail
