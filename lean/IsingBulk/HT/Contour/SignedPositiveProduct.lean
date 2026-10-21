import IsingBulk.HT.Contour.SignedPositivePower

/-! Attachment of the positive coarea integral to all original arclength factors. -/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.Branch IsingBulk.Tail IsingBulk.HT.Lie Set MeasureTheory
open scoped BigOperators

theorem shiftedWeightedPhaseSpectatorKernel_update_product {N : ℕ} (p q : Fin N) (hpq : p ≠ q)
    (α β shiftY shiftZ : ℝ) (L : ℝ → ℝ) (F G : (Fin N → ℝ) → ℝ) (u : Fin N → ℝ) :
    L (u p)*L (u q)*shiftedWeightedPhaseSpectatorKernel p q α β shiftY shiftZ L (twoPhaseUpdate F G p q u) =
      (∏ i, L (u i))*shiftedTwoPhaseKernel α β shiftY shiftZ (F u,G u) := by
  rw [shiftedWeightedPhaseSpectatorKernel_factorization p q hpq]
  have he : (∏ i ∈ (Finset.univ.erase p).erase q, L (twoPhaseUpdate F G p q u i)) =
      ∏ i ∈ (Finset.univ.erase p).erase q, L (u i) := by
    apply Finset.prod_congr rfl
    intro i hi
    have hiq := (Finset.mem_erase.mp hi).1
    have hip := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
    simp [twoPhaseUpdate,hip,hiq]
  rw [he,← Finset.mul_prod_erase Finset.univ (fun i => L (u i)) (Finset.mem_univ p),
    ← Finset.mul_prod_erase (Finset.univ.erase p) (fun i => L (u i))
      (Finset.mem_erase.mpr ⟨hpq.symm,Finset.mem_univ q⟩)]
  simp only [twoPhaseUpdate,ite_true,hpq.symm,ite_false,shiftedTwoPhaseKernel]
  ring

def signedPositiveKernel {N : ℕ} (d : LocalBranchData) (ε α β shiftY shiftZ : ℝ)
    (u : Fin N → ℝ) : ℝ :=
  (∏ i, ‖deriv (originalPhase d ε) (u i)‖)*
    shiftedTwoPhaseKernel α β shiftY shiftZ ((∑ i, u i)-(N:ℝ)*d.thetaB,allBranchExteriorTotalPhase d ε u)

theorem signed_positive_kernel_nonneg {N : ℕ} (d : LocalBranchData)
    (ε α β shiftY shiftZ : ℝ) (u : Fin N → ℝ) : 0 ≤ signedPositiveKernel d ε α β shiftY shiftZ u :=
  mul_nonneg (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) (shiftedTwoPhaseKernel_nonneg _ _ _ _ _)

theorem signed_positive_kernel_factorization {N : ℕ} (d : LocalBranchData)
    (ε α β shiftY shiftZ : ℝ) (p q : Fin N) (hpq : p ≠ q) (u : Fin N → ℝ) :
    ‖deriv (originalPhase d ε) (u p)*deriv (originalPhase d ε) (u q)‖*
      shiftedWeightedPhaseSpectatorKernel p q α β shiftY shiftZ (fun t => ‖deriv (originalPhase d ε) t‖)
        (allBranchExteriorCoordinateMap d ε p q u) = signedPositiveKernel d ε α β shiftY shiftZ u := by
  rw [norm_mul]
  exact shiftedWeightedPhaseSpectatorKernel_update_product p q hpq α β shiftY shiftZ
    (fun t => ‖deriv (originalPhase d ε) t‖)
    (fun v => (∑ i, v i)-(N:ℝ)*d.thetaB) (allBranchExteriorTotalPhase d ε) u

theorem signed_positive_power_product_integral {N : ℕ} {d : LocalBranchData}
    (B : BranchEstimates d) (ε a D R α β shiftY shiftZ : ℝ) (P : ℕ) (p q : Fin N) (hpq : p ≠ q)
    (hε : 0 < ε) (hεr : ε ≤ B.ε₀) (ha : 0 < a) (hD : 0 < D)
    (hsmall₁ : B.original.separationThreshold*ε ≤ a) (hsmall₂ : 2*B.original.C₀*ε ≤ a)
    (hR : 0 ≤ R) (hRB : R ≤ B.r) (hRπ : R ≤ Real.pi)
    (hα : 0 < α) (hα1 : α ≤ 1) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    IntegrableOn (fun u => (u q-u p)^(P+1)*signedPositiveKernel d ε α β shiftY shiftZ u)
      (allBranchExteriorPositiveGapCell p q R a D) ∧
    (∫ u in allBranchExteriorPositiveGapCell p q R a D,
      (u q-u p)^(P+1)*signedPositiveKernel d ε α β shiftY shiftZ u) ≤
      (D^(P+1)*allBranchExteriorPositiveCost B a D)*
        (((N:ℝ)*simpleKernelConstant*(1+|Real.log α|))*
          ((N:ℝ)*simpleKernelConstant*(1+|Real.log β|))*B.lengthC^(N-2)) := by
  have hh := signed_positive_power_master_integral B ε a D R α β shiftY shiftZ P p q hpq
    hε hεr ha hD hsmall₁ hsmall₂ hR hRB hRπ hα hα1 hβ hβ1
  dsimp only at hh
  simpa only [mul_assoc,signed_positive_kernel_factorization d ε α β shiftY shiftZ p q hpq] using hh

end
end IsingBulk.HT.Contour
