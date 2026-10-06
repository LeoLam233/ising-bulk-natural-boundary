import IsingBulk.Tail.MixedActualDensityExpansion
import IsingBulk.Tail.MicrocorePointwiseBudget

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets Set Filter
open scoped Topology BigOperators

theorem mixedActiveParameterDirection_norm (N : ℕ) : ‖mixedActiveParameterDirection N‖≤1 := by
  simp [mixedActiveParameterDirection,Prod.norm_def]

theorem mixedActiveBranchDirection_norm {N : ℕ} (j : Fin N) : ‖mixedActiveBranchDirection j‖≤1 := by
  simp [mixedActiveBranchDirection,Prod.norm_def,Pi.norm_single]

theorem mixedActiveCompactDirection_norm (N : ℕ) : ‖mixedActiveCompactDirection N‖≤1 := by
  simp [mixedActiveCompactDirection,Prod.norm_def]

/-- The exact source expansion has polynomial iteration cost, with its
simple kernels and branch volume still exposed for absolute integration. -/
theorem mixedDensityJetTerms_pointwise_budget {N : ℕ}
    (J : Finset (Fin N)) (j q : Fin N) (f : SelectorFunctions) (r τ lam : ℝ)
    (s : ℂ) (θ : Fin N → ℝ) (C : ℂ) (w : (Fin N → ℝ) → ℝ)
    (R₁ R₂ F : MixedActiveSpace N → ℂ) (V : Fin N → MixedActiveSpace N → ℂ)
    (order k : ℕ) (hk : k≤order) (A B D : ℝ) (hA : 1≤A)
    (hR₁ : JetBound R₁ 0 (order+1) A) (hR₂ : JetBound R₂ 0 (order+1) A)
    (hV : ∀ i,JetBound (V i) 0 order A) (hF : JetBound F 0 order D)
    (hcut : ∀ l : List (Fin N),l.length≤k → |cutoffJet l w θ|≤B) :
    ‖((mixedDensityJetTerms (mixedActiveParameterDirection N) (mixedActiveBranchDirection j)
      (mixedActiveCompactDirection N) R₁ R₂ F V k).map
        (fun T => T.sourceValue J q f r τ lam s θ C w s θ)).sum‖ ≤
    ((N+1:ℕ):ℝ)^k*(B*‖C‖*‖mixedSimpleKernel f r τ lam s θ‖*‖mixedHybridVolume J f r τ lam s θ‖*
      ((1+4*2^order*A)^k*D)) := by
  let L := mixedDensityJetTerms (mixedActiveParameterDirection N) (mixedActiveBranchDirection j)
    (mixedActiveCompactDirection N) R₁ R₂ F V k
  let P := ‖C‖*‖mixedSimpleKernel f r τ lam s θ‖*‖mixedHybridVolume J f r τ lam s θ‖
  let M := (1+4*2^order*A)^k*D
  have hP : 0≤P := by dsimp [P]; positivity
  have hB : 0≤B := (abs_nonneg (cutoffJet [] w θ)).trans (hcut [] (by simp))
  have hbudget := mixedDensityJetTerms_jet_budget (mixedActiveParameterDirection N) (mixedActiveBranchDirection j)
    (mixedActiveCompactDirection N) (mixedActiveParameterDirection_norm N) (mixedActiveBranchDirection_norm j)
    (mixedActiveCompactDirection_norm N) R₁ R₂ F V 0 order k hk A D hA hR₁ hR₂ hV hF
  have hb := norm_list_sum_le_length_mul (L.map (fun T => T.sourceValue J q f r τ lam s θ C w s θ))
    (B*P*M) (by
      intro a ha
      obtain ⟨T,hT,rfl⟩ := List.mem_map.mp ha
      have hreg : ‖T.regularPart 0‖≤M := by
        simpa only [norm_iteratedFDeriv_zero] using (hbudget T hT).bound 0 (Nat.zero_le _)
      have hc := hcut T.cutoff (mixedDensityJetTerms_cutoff_length _ _ _ R₁ R₂ F V k T hT)
      calc
        ‖T.sourceValue J q f r τ lam s θ C w s θ‖=|cutoffJet T.cutoff w θ| *(P*‖T.regularPart 0‖) := by
          simp only [MixedDensityJetTerm.sourceValue,mixedAnalyticDensityModel,mixedRegularPullback,
            mixedFreeze_self,mixedSourceDisplacement_zero,norm_mul,Complex.norm_real,Real.norm_eq_abs]
          dsimp [P]
          ring
        _ ≤ B*(P*M) := mul_le_mul hc (mul_le_mul_of_nonneg_left hreg hP)
          (mul_nonneg hP (norm_nonneg _)) hB
        _ = B*P*M := by ring)
  have hlen : L.length=(N+1)^k := mixedDensityJetTerms_length _ _ _ R₁ R₂ F V k
  rw [List.length_map,hlen,Nat.cast_pow] at hb
  apply hb.trans_eq
  dsimp [P,M]
  ring

end
end IsingBulk.Tail
