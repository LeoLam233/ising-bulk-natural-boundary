import IsingBulk.AnisoF002.C03.IsotropicFiniteJetControl

/-!
# Finite smooth jet control survives inversion near the identity

Only real smoothness of the input is used. Complex analyticity belongs
to the generic inversion map on the Banach algebra; the actual angular
coefficients and cutoffs are never continued analytically.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set

def inverseFiniteJetConstant (k : ℕ) : ℝ :=
  (k.factorial : ℝ) * (1 + ∑ i ∈ Finset.range (k + 1), 4 * protectedJetConstant i (1 / 4 : ℝ))

theorem inverseFiniteJetConstant_pos (k : ℕ) : 0 < inverseFiniteJetConstant k := by
  have hsum : 0 ≤ ∑ i ∈ Finset.range (k + 1), 4 * protectedJetConstant i (1 / 4 : ℝ) :=
    Finset.sum_nonneg (fun i _ => (mul_pos (by norm_num) (protectedJetConstant_pos i (by norm_num))).le)
  have hfact : 0 < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  unfold inverseFiniteJetConstant
  positivity

variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [NormOneClass A]

theorem FiniteJetControl.banach_inverse {k : ℕ} {f : E → A} {C : ℝ}
    (hf : FiniteJetControl k f C) (hC : 1 ≤ C)
    (hnear : ∀ x, ‖f x - 1‖ ≤ (1 / 2 : ℝ)) :
    FiniteJetControl k (fun x => Ring.inverse (f x)) (inverseFiniteJetConstant k * C ^ k) := by
  have ha (x : E) : AnalyticAt ℂ Ring.inverse (f x) :=
    ((banach_inverse_protected_ball (f x) (hnear x)) (f x)
      (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1 / 4))).1
  have hs : ContDiff ℝ k (fun x => Ring.inverse (f x)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    exact (ha x).restrictScalars.contDiffAt.comp x hf.smooth.contDiffAt
  refine ⟨hs, ?_⟩
  intro m hm x
  let Q := 1 + ∑ i ∈ Finset.range (k + 1), 4 * protectedJetConstant i (1 / 4 : ℝ)
  have hsum : 0 ≤ ∑ i ∈ Finset.range (k + 1), 4 * protectedJetConstant i (1 / 4 : ℝ) :=
    Finset.sum_nonneg (fun i _ => (mul_pos (by norm_num) (protectedJetConstant_pos i (by norm_num))).le)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have houter : ∀ i, i ≤ m → ‖iteratedFDeriv ℝ i Ring.inverse (f x)‖ ≤ Q := by
    intro i hi
    have hterm : 4 * protectedJetConstant i (1 / 4 : ℝ) ≤
        ∑ l ∈ Finset.range (k + 1), 4 * protectedJetConstant l (1 / 4 : ℝ) :=
      Finset.single_le_sum
        (fun l _ => (mul_pos (by norm_num) (protectedJetConstant_pos l (by norm_num))).le)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le (hi.trans hm)))
    exact (banach_inverse_real_jet_bound (f x) (hnear x) i).trans
      (by dsimp [Q]; linarith only [hterm])
  have hinner : ∀ i, 1 ≤ i → i ≤ m → ‖iteratedFDeriv ℝ i f x‖ ≤ C ^ i := by
    intro i hi him
    have hpow : C ≤ C ^ i := by simpa only [pow_one] using pow_le_pow_right₀ hC hi
    exact (hf.bound i (him.trans hm) x).trans hpow
  have hh := norm_iteratedFDeriv_comp_at_le f Ring.inverse x m
    (hf.smooth.of_le (by exact_mod_cast hm)).contDiffAt (ha x).restrictScalars.contDiffAt
    Q C houter hinner
  have hfact : (m.factorial : ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_le hm
  have hpow : C ^ m ≤ C ^ k := pow_le_pow_right₀ hC hm
  exact hh.trans ((mul_le_mul (mul_le_mul_of_nonneg_right hfact hQ) hpow
    (by positivity) (by positivity)).trans_eq (by rfl))

end IsingBulk.AnisoF002.Isotropic
