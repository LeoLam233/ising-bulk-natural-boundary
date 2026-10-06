import IsingBulk.Tail.DeformedPointRealJets
import IsingBulk.Tail.RealPolynomialJets
import Mathlib.Analysis.Calculus.MeanValue

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First Set
open scoped Topology ContDiff
set_option maxHeartbeats 1500000

theorem deformedPoint_diagonal {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ)
    (θ : Fin N → ℝ) (i j : Fin N) (he : θ i=θ j) :
    deformedPoint f r τ lam θ i=deformedPoint f r τ lam θ j := by
  unfold deformedPoint retractionShift
  dsimp only
  rw [he]

theorem deformedPoint_difference_value (f : SelectorFunctions) (hf : RegularSelector f) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N → ∀ r τ lam : ℝ,
      0 ≤ r → r ≤ 1 → 0 ≤ τ → τ ≤ 1 → 0 ≤ lam → lam ≤ 1 →
      ∀ i j : Fin N, ∀ θ : Fin N → ℝ,
      ‖deformedPoint f r τ lam θ i-deformedPoint f r τ lam θ j‖ ≤ C*|θ i-θ j| := by
  obtain ⟨C,hC,hjets⟩ := deformedPoint_real_finite_jets f hf 1
  refine ⟨2*C,by positivity,?_⟩
  intro N hN r τ lam hr hr1 hτ hτ1 hlam hlam1 i j θ
  by_cases hij : i=j
  · subst j; simp
  let θ0 := Function.update θ i (θ j)
  let F := fun x => deformedPoint f r τ lam x i-deformedPoint f r τ lam x j
  have hdiag : F θ0=0 := by
    apply sub_eq_zero.mpr
    exact deformedPoint_diagonal f r τ lam θ0 i j (by simp [θ0,Ne.symm hij])
  have hsm (l : Fin N) := deformedPoint_fixed_contDiff f r τ lam hf.p_smooth hf.m_smooth l
  have hFs : ContDiff ℝ ∞ F := (hsm i).sub (hsm j)
  have hFb (x : Fin N → ℝ) : ‖fderiv ℝ F x‖ ≤ 2*C := by
    have hi := hjets N hN r τ lam hr hr1 hτ hτ1 hlam hlam1 i x 1 le_rfl
    have hj := hjets N hN r τ lam hr hr1 hτ hτ1 hlam hlam1 j x 1 le_rfl
    rw [norm_iteratedFDeriv_one] at hi hj
    change ‖fderiv ℝ (fun x => deformedPoint f r τ lam x i-deformedPoint f r τ lam x j) x‖ ≤ _
    rw [fderiv_fun_sub ((hsm i).differentiable (by simp) x) ((hsm j).differentiable (by simp) x)]
    exact (norm_sub_le _ _).trans (by linarith)
  have hdist : ‖θ-θ0‖ ≤ |θ i-θ j| := by
    apply (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr
    intro l
    by_cases hl : l=i
    · subst l; simp [θ0,Real.norm_eq_abs]
    · simp [θ0,Function.update_of_ne hl,abs_nonneg]
  have hh := (convex_univ : Convex ℝ (univ : Set (Fin N → ℝ))).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => hFs.differentiable (by simp) x) (fun x _ => hFb x) (mem_univ θ0) (mem_univ θ)
  rw [hdiag,sub_zero] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hdist (by positivity))

theorem deformedPoint_difference_scaled_jets (f : SelectorFunctions) (hf : RegularSelector f)
    (J : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N → ∀ r τ lam : ℝ,
      0 ≤ r → r ≤ 1 → 0 ≤ τ → τ ≤ 1 → 0 ≤ lam → lam ≤ 1 →
      ∀ i j : Fin N, ∀ p : ℂ × (Fin N → ℝ), ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      |p.2 i-p.2 j| ≤ ρ →
      RealScaledJetBound (fun q : ℂ × (Fin N → ℝ) =>
        deformedPoint f r τ lam q.2 i-deformedPoint f r τ lam q.2 j) p J ρ C 1 := by
  obtain ⟨A,hA,hv⟩ := deformedPoint_difference_value f hf
  obtain ⟨B,hB,hj⟩ := deformedPoint_joint_finite_jets f hf J
  refine ⟨A+2*B,by positivity,?_⟩
  intro N hN r τ lam hr hr1 hτ hτ1 hlam hlam1 i j p ρ hρ hρ1 hsel
  have hsm (l : Fin N) : ContDiff ℝ ∞ (fun q : ℂ × (Fin N → ℝ) => deformedPoint f r τ lam q.2 l) :=
    (deformedPoint_fixed_contDiff f r τ lam hf.p_smooth hf.m_smooth l).comp contDiff_snd
  refine ⟨((hsm i).sub (hsm j)).contDiffAt,by positivity,?_⟩
  intro k hk
  cases k with
  | zero =>
    simp only [norm_iteratedFDeriv_zero,Nat.cast_zero,sub_zero,zpow_one]
    exact ((hv N hN r τ lam hr hr1 hτ hτ1 hlam hlam1 i j p.2).trans
      (mul_le_mul_of_nonneg_left hsel hA.le)).trans
      (mul_le_mul_of_nonneg_right (by linarith) hρ.le)
  | succ k =>
    rw [fun_iteratedFDeriv_sub_apply ((hsm i).of_le (show ((k+1:ℕ):ℕ∞ω) ≤ ∞ by simp)).contDiffAt
      ((hsm j).of_le (show ((k+1:ℕ):ℕ∞ω) ≤ ∞ by simp)).contDiffAt]
    have hb : ‖iteratedFDeriv ℝ (k+1) (fun q : ℂ × (Fin N → ℝ) => deformedPoint f r τ lam q.2 i) p‖+
        ‖iteratedFDeriv ℝ (k+1) (fun q : ℂ × (Fin N → ℝ) => deformedPoint f r τ lam q.2 j) p‖ ≤ 2*B := by
      have hi := hj N hN r τ lam hr hr1 hτ hτ1 hlam hlam1 i p (k+1) hk
      have hj' := hj N hN r τ lam hr hr1 hτ hτ1 hlam hlam1 j p (k+1) hk
      linarith
    apply (norm_sub_le _ _).trans (hb.trans _)
    have hp : 1 ≤ ρ^(1-((k+1:ℕ):ℤ)) := by
      rw [show (1-((k+1:ℕ):ℤ))=-(k:ℤ) by omega,zpow_neg,zpow_natCast,← inv_pow]
      exact one_le_pow₀ ((one_le_inv₀ hρ).mpr hρ1)
    exact (show 2*B ≤ A+2*B by linarith).trans (le_mul_of_one_le_right (by positivity) hp)

end
end IsingBulk.Tail
