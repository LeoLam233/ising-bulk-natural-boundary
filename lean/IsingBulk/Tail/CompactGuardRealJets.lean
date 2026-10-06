import IsingBulk.Tail.AllBranchExteriorGuardJets
import IsingBulk.Tail.CompactWeightedLieJets
import IsingBulk.Tail.RealDeterminantJets

namespace IsingBulk.Tail
noncomputable section
open Filter
open scoped Topology ContDiff BigOperators
set_option maxHeartbeats 1800000

theorem selectedGuardScalar_iteratedDeriv (h : ℝ) (k : ℕ) :
    iteratedDeriv k (allBranchSelectedGuardFactor h 0)=allBranchSelectedGuardFactor h k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iteratedDeriv_succ,ih]
    exact funext (fun t => (allBranchSelectedGuardFactor_hasDerivAt h k t).deriv)

theorem selectedGuardScalar_distance_jets (J : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ h : ℝ, 0 < h → ∀ t : ℝ, t ≠ 0 → ∀ k ≤ J,
      ‖iteratedFDeriv ℝ k (allBranchSelectedGuardFactor h 0) t‖ ≤ C*(|t|⁻¹)^k := by
  obtain ⟨C,hC,hjets⟩ := allBranchSelectedGuard_distance_jets J
  refine ⟨C,hC,?_⟩
  intro h hh t ht k hk
  have hb := hjets 2 h hh 0 1 ![t,0] (by simpa using ht) (List.replicate k 0) (by simpa) 
  rw [allBranchSelectedGuard_word] at hb
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,selectedGuardScalar_iteratedDeriv]
  simpa using hb

/-- The guard is estimated at the actual selected separation, uniformly in
the cutoff radius. This avoids a diverging cutoff cost in the removal limit. -/
theorem compact_selected_guard_real_jets (J : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ N : ℕ, ∀ h : ℝ, 0 < h → ∀ i j : Fin N,
      ∀ p : ℂ × (Fin N → ℝ), ∀ ρ : ℝ, 0 < ρ → ρ ≤ |p.2 i-p.2 j| →
      RealScaledJetBound (fun q : ℂ × (Fin N → ℝ) => (allBranchSelectedGuard h i j q.2:ℂ))
        p J ρ (C*2^J) 0 := by
  obtain ⟨C,hC,hjets⟩ := selectedGuardScalar_distance_jets J
  refine ⟨C,hC,?_⟩
  intro N h hh i j p ρ hρ hρgap
  let g := allBranchSelectedGuardFactor h 0
  have hg : ContDiff ℝ ∞ g := by
    have he : g=(fun t => 1-microCutoffBase (t/h)) := by
      funext t
      simp [g,allBranchSelectedGuardFactor,scaledCutoffFactor]
    rw [he]
    exact contDiff_const.sub ((fixedBranchBump 1 (by norm_num)).contDiff.comp (contDiff_id.div_const h))
  let L : (ℂ × (Fin N → ℝ)) →L[ℝ] ℝ :=
    ((ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ)-(ContinuousLinearMap.proj j)).comp
      (ContinuousLinearMap.snd ℝ ℂ (Fin N → ℝ))
  have hL : ‖L‖ ≤ 2 := L.opNorm_le_bound (by norm_num) (fun q => by
    calc
      ‖L q‖ = ‖q.2 i-q.2 j‖ := rfl
      _ ≤ ‖q.2 i‖+‖q.2 j‖ := norm_sub_le _ _
      _ ≤ ‖q‖+‖q‖ := add_le_add ((norm_le_pi_norm q.2 i).trans (norm_snd_le q))
        ((norm_le_pi_norm q.2 j).trans (norm_snd_le q))
      _ = _ := by ring)
  have hgL : ContDiff ℝ ∞ (g ∘ L) := hg.comp L.contDiff
  have heF : (fun q : ℂ × (Fin N → ℝ) => (allBranchSelectedGuard h i j q.2:ℂ))=
      Complex.ofRealCLM ∘ g ∘ L := by
    funext q
    simp [allBranchSelectedGuard,g,allBranchSelectedGuardFactor,scaledCutoffFactor,L]
  rw [heF]
  have hgap : 0 < |p.2 i-p.2 j| := hρ.trans_le hρgap
  refine ⟨(Complex.ofRealCLM.contDiff.comp hgL).contDiffAt,by positivity,?_⟩
  intro k hk
  have hb : ‖iteratedFDeriv ℝ k g (L p)‖ ≤ C*(ρ⁻¹)^k :=
    (hjets h hh (p.2 i-p.2 j) (abs_pos.mp hgap) k hk).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (inv_nonneg.mpr hgap.le) (inv_anti₀ hρ hρgap) k) (zero_le_one.trans hC))
  have hc : ‖Complex.ofRealCLM‖ ≤ 1 :=
    Complex.ofRealCLM.opNorm_le_bound zero_le_one (fun x => by simp)
  have hcast := Complex.ofRealCLM.norm_iteratedFDeriv_comp_left (x := p) hgL.contDiffAt
    (by simp : (k:ℕ∞ω) ≤ ∞)
  apply (hcast.trans (mul_le_of_le_one_left (norm_nonneg _) hc)).trans
  rw [L.iteratedFDeriv_comp_right hg p (by simp)]
  apply ((iteratedFDeriv ℝ k g (L p)).norm_compContinuousLinearMap_le _).trans
  have hprod : (∏ _l : Fin k, ‖L‖) ≤ (2:ℝ)^J := by
    simpa using (pow_le_pow_left₀ (norm_nonneg L) hL k).trans
      (pow_le_pow_right₀ (by norm_num) hk)
  calc
    _ ≤ (C*(ρ⁻¹)^k)*2^J := mul_le_mul hb hprod (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) (by positivity)
    _ = _ := by rw [zero_sub,zpow_neg,zpow_natCast,← inv_pow]; ring

end
end IsingBulk.Tail
