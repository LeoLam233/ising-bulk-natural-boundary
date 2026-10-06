import IsingBulk.Tail.CompactPhaseJointJets
import IsingBulk.Tail.CompactDeterminantJets
import IsingBulk.Tail.RealScaledJetBounds

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First Filter
open scoped Topology ContDiff BigOperators
set_option maxHeartbeats 1500000

theorem logYBaseline_positive_jet_bound (N k : ℕ) (hk : 1 ≤ k) (θ : Fin N → ℝ) :
    ‖iteratedFDeriv ℝ k (logYBaseline N) θ‖ ≤ N := by
  have hL : ‖logYBaselineLinear N‖ ≤ N := by
    apply (logYBaselineLinear N).opNorm_le_bound (by positivity)
    intro x
    rw [logYBaselineLinear_apply]
    simp only [logYBaseline,norm_mul,Complex.norm_I,one_mul]
    calc
      _ ≤ ∑ i, ‖(x i:ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin N, ‖x‖ := Finset.sum_le_sum (fun i _ => by
        simpa only [Complex.norm_real] using norm_le_pi_norm x i)
      _ = _ := by simp
  have he : logYBaseline N=(logYBaselineLinear N : (Fin N → ℝ) → ℂ) :=
    funext (fun x => (logYBaselineLinear_apply x).symm)
  rw [he]
  obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rw [← norm_iteratedFDeriv_fderiv]
  have hd : fderiv ℝ (logYBaselineLinear N)=(fun _ => logYBaselineLinear N) :=
    funext (fun _ => (logYBaselineLinear N).fderiv)
  rw [hd]
  cases l with
  | zero => simpa using hL
  | succ l => simp [iteratedFDeriv_succ_const]

theorem unwrappedLogY_positive_finite_jets (f : SelectorFunctions) (hf : RegularSelector f)
    (J : ℕ) : ∃ C : ℝ, 1 ≤ C ∧ ∀ N : ℕ, 0 < N → ∀ r τ lam : ℝ,
      0 ≤ τ → τ ≤ 1 → 0 ≤ lam → lam ≤ 1 → ∀ θ : Fin N → ℝ,
      ∀ k, 1 ≤ k → k ≤ J → ‖iteratedFDeriv ℝ k (unwrappedLogY f r τ lam) θ‖ ≤ C*N := by
  induction J with
  | zero => exact ⟨1,le_rfl,by intros; omega⟩
  | succ J ih =>
    obtain ⟨C,hC,hb⟩ := ih
    obtain ⟨D,hD,hd⟩ := unwrappedLogY_positive_jet_perturbation f hf.p_smooth hf.m_smooth
      hf.p_periodic hf.m_periodic (J+1) (by omega)
    refine ⟨max C (D+1),hC.trans (le_max_left _ _),?_⟩
    intro N hN r τ lam hτ hτ1 hlam hlam1 θ k hk hkJ
    by_cases hk' : k ≤ J
    · exact (hb N hN r τ lam hτ hτ1 hlam hlam1 θ k hk hk').trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    · have hek : k=J+1 := by omega
      subst k
      have hn : (0:ℝ) ≤ N := by positivity
      calc
        _ ≤ ‖iteratedFDeriv ℝ (J+1) (unwrappedLogY f r τ lam) θ-
              iteratedFDeriv ℝ (J+1) (logYBaseline N) θ‖+
            ‖iteratedFDeriv ℝ (J+1) (logYBaseline N) θ‖ := by
          simpa only [sub_add_cancel] using norm_add_le
            (iteratedFDeriv ℝ (J+1) (unwrappedLogY f r τ lam) θ-
              iteratedFDeriv ℝ (J+1) (logYBaseline N) θ)
            (iteratedFDeriv ℝ (J+1) (logYBaseline N) θ)
        _ ≤ D*N*lam+N := add_le_add (hd N hN r τ lam hτ hτ1 hlam θ)
          (logYBaseline_positive_jet_bound N (J+1) (by omega) θ)
        _ ≤ (D+1)*N := by nlinarith [mul_nonneg hD.le hn]
        _ ≤ max C (D+1)*N := mul_le_mul_of_nonneg_right (le_max_right _ _) hn

theorem unwrappedLogY_joint_positive_finite_jets (f : SelectorFunctions) (hf : RegularSelector f)
    (J : ℕ) : ∃ C : ℝ, 1 ≤ C ∧ ∀ N : ℕ, 0 < N → ∀ r τ lam : ℝ,
      0 ≤ τ → τ ≤ 1 → 0 ≤ lam → lam ≤ 1 → ∀ p : ℂ × (Fin N → ℝ),
      ∀ k, 1 ≤ k → k ≤ J →
      ‖iteratedFDeriv ℝ k (fun q : ℂ × (Fin N → ℝ) => unwrappedLogY f r τ lam q.2) p‖ ≤ C*N := by
  obtain ⟨C,hC,hb⟩ := unwrappedLogY_positive_finite_jets f hf J
  refine ⟨C,hC,?_⟩
  intro N hN r τ lam hτ hτ1 hlam hlam1 p k hk hkJ
  let L := ContinuousLinearMap.snd ℝ ℂ (Fin N → ℝ)
  have hL : ‖L‖ ≤ 1 := L.opNorm_le_bound zero_le_one (fun x => by
    simpa [L] using norm_snd_le x)
  exact (jet_comp_contraction_right L hL _
    (unwrappedLogY_contDiff f r τ lam hf.p_smooth hf.m_smooth) p k).trans
      (hb N hN r τ lam hτ hτ1 hlam hlam1 p.2 k hk hkJ)

end
end IsingBulk.Tail
