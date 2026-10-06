import IsingBulk.Tail.AllBranchExteriorWeightedPositive

/-! Attachment of the positive coarea integral to all original arclength factors. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch Set MeasureTheory
open scoped BigOperators

theorem weightedPhaseSpectatorKernel_update_product {N : ℕ} (p q : Fin N) (hpq : p ≠ q)
    (α β : ℝ) (L : ℝ → ℝ) (F G : (Fin N → ℝ) → ℝ) (u : Fin N → ℝ) :
    L (u p)*L (u q)*weightedPhaseSpectatorKernel p q α β L (twoPhaseUpdate F G p q u) =
      (∏ i, L (u i))*twoPhaseKernel α β (F u,G u) := by
  rw [weightedPhaseSpectatorKernel_factorization p q hpq]
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
  simp only [coordinatePhaseKernel,twoPhaseUpdate,ite_true,hpq.symm,ite_false,twoPhaseKernel]
  ring

def allBranchExteriorPositiveKernel {N : ℕ} (d : LocalBranchData) (ε α β : ℝ)
    (u : Fin N → ℝ) : ℝ :=
  (∏ i, ‖deriv (originalPhase d ε) (u i)‖)*
    twoPhaseKernel α β ((∑ i, u i)-(N:ℝ)*d.thetaB,allBranchExteriorTotalPhase d ε u)

theorem allBranchExterior_positive_kernel_nonneg {N : ℕ} (d : LocalBranchData)
    (ε α β : ℝ) (u : Fin N → ℝ) : 0 ≤ allBranchExteriorPositiveKernel d ε α β u :=
  mul_nonneg (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) (twoPhaseKernel_nonneg _ _ _)

theorem allBranchExterior_positive_kernel_factorization {N : ℕ} (d : LocalBranchData)
    (ε α β : ℝ) (p q : Fin N) (hpq : p ≠ q) (u : Fin N → ℝ) :
    ‖deriv (originalPhase d ε) (u p)*deriv (originalPhase d ε) (u q)‖*
      weightedPhaseSpectatorKernel p q α β (fun t => ‖deriv (originalPhase d ε) t‖)
        (allBranchExteriorCoordinateMap d ε p q u) = allBranchExteriorPositiveKernel d ε α β u := by
  rw [norm_mul]
  exact weightedPhaseSpectatorKernel_update_product p q hpq α β
    (fun t => ‖deriv (originalPhase d ε) t‖)
    (fun v => (∑ i, v i)-(N:ℝ)*d.thetaB) (allBranchExteriorTotalPhase d ε) u

theorem allBranchExterior_positive_power_product_integral {N : ℕ} {d : LocalBranchData}
    (B : BranchEstimates d) (ε a D R α β : ℝ) (P : ℕ) (p q : Fin N) (hpq : p ≠ q)
    (hε : 0 < ε) (hεr : ε ≤ B.ε₀) (ha : 0 < a) (hD : 0 < D)
    (hsmall₁ : B.original.separationThreshold*ε ≤ a) (hsmall₂ : 2*B.original.C₀*ε ≤ a)
    (hR : 0 ≤ R) (hRB : R ≤ B.r) (hRπ : R ≤ Real.pi)
    (hα : 0 < α) (hα1 : α ≤ 1) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    IntegrableOn (fun u => (u q-u p)^(P+1)*allBranchExteriorPositiveKernel d ε α β u)
      (allBranchExteriorPositiveGapCell p q R a D) ∧
    (∫ u in allBranchExteriorPositiveGapCell p q R a D,
      (u q-u p)^(P+1)*allBranchExteriorPositiveKernel d ε α β u) ≤
      (D^(P+1)*allBranchExteriorPositiveCost B a D)*
        (((N:ℝ)*simpleKernelConstant*(1+|Real.log α|))*
          ((N:ℝ)*simpleKernelConstant*(1+|Real.log β|))*B.lengthC^(N-2)) := by
  have hh := allBranchExterior_positive_power_master_integral B ε a D R α β P p q hpq
    hε hεr ha hD hsmall₁ hsmall₂ hR hRB hRπ hα hα1 hβ hβ1
  dsimp only at hh
  simpa only [mul_assoc,allBranchExterior_positive_kernel_factorization d ε α β p q hpq] using hh

end
end IsingBulk.Tail
