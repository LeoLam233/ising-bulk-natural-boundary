import IsingBulk.Tail.OnePhaseSumIntegral
import IsingBulk.Tail.AllBranchExteriorPositiveMaster
import IsingBulk.Tail.ReciprocalDistanceIntegral

/-! Actual branch arclength spectators for the negative-coordinate split. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch Set MeasureTheory
open scoped BigOperators

def allBranchExteriorOnePhaseKernel {N : ℕ} (d : LocalBranchData) (ε α : ℝ)
    (p : Fin N) (u : Fin N → ℝ) : ℝ :=
  (phaseDenominator (Real.exp (-α)) ((∑ i, u i)-(N:ℝ)*d.thetaB))⁻¹*
    ∏ i ∈ Finset.univ.erase p, ‖deriv (originalPhase d ε) (u i)‖

def allBranchExteriorLogPhaseKernel {N : ℕ} (d : LocalBranchData) (ε α : ℝ)
    (p v : Fin N) (u : Fin N → ℝ) : ℝ :=
  (phaseDenominator (Real.exp (-α)) ((∑ i, u i)-(N:ℝ)*d.thetaB))⁻¹*
    (|u v|+ε)⁻¹*(∏ i ∈ (Finset.univ.erase p).erase v, ‖deriv (originalPhase d ε) (u i)‖)

theorem allBranchExterior_one_phase_integral {N : ℕ} {d : LocalBranchData}
    (B : BranchEstimates d) (p q : Fin N) (hpq : p ≠ q) {ε R α : ℝ}
    (hε : 0 < ε) (hεr : ε ≤ B.ε₀) (hR : 0 ≤ R) (hRB : R ≤ B.r) (hRπ : R ≤ Real.pi)
    (hα : 0 < α) (hα1 : α ≤ 1) :
    IntegrableOn (allBranchExteriorOnePhaseKernel d ε α p) (Icc (fun _ => -R) (fun _ => R)) ∧
    (∫ u in Icc (fun _ => -R) (fun _ => R), allBranchExteriorOnePhaseKernel d ε α p u) ≤
      ((N:ℝ)*simpleKernelConstant*(1+|Real.log α|))*B.lengthC^(N-1) := by
  have hL := allBranchExterior_arclength_continuousOn B ε R hε hεr hRB
  have hLint := (B.length_restrict ε hε hεr (Icc (-R) R) (by
    intro t ht
    constructor <;> linarith [ht.1,ht.2])).2
  have hh := one_phase_sum_weighted_integral (b := d.thetaB) p q hpq
    (fun _ t => ‖deriv (originalPhase d ε) t‖) (fun _ => B.lengthC) (fun _ _ => norm_nonneg _)
    hR hRπ hα hα1 (fun _ => hL) (fun _ => hLint)
  unfold allBranchExteriorOnePhaseKernel
  simpa only [Finset.prod_const,Finset.card_erase_of_mem
    (Finset.mem_univ p),Finset.card_univ,Fintype.card_fin] using hh

theorem allBranchExterior_log_phase_integral {N : ℕ} {d : LocalBranchData}
    (B : BranchEstimates d) (p v : Fin N) (hpv : p ≠ v) {ε R α : ℝ}
    (hε : 0 < ε) (hεr : ε ≤ B.ε₀) (hR : 0 ≤ R) (hRB : R ≤ B.r) (hRπ : R ≤ Real.pi)
    (hα : 0 < α) (hα1 : α ≤ 1) :
    IntegrableOn (allBranchExteriorLogPhaseKernel d ε α p v) (Icc (fun _ => -R) (fun _ => R)) ∧
    (∫ u in Icc (fun _ => -R) (fun _ => R), allBranchExteriorLogPhaseKernel d ε α p v u) ≤
      ((N:ℝ)*simpleKernelConstant*(1+|Real.log α|))*(2*Real.log ((R+ε)/ε))*B.lengthC^(N-2) := by
  classical
  let L := fun i : Fin N => if i=v then (fun t : ℝ => (|t|+ε)⁻¹)
    else (fun t => ‖deriv (originalPhase d ε) t‖)
  let C := fun i : Fin N => if i=v then 2*Real.log ((R+ε)/ε) else B.lengthC
  have hL0 : ∀ i t, 0 ≤ L i t := by
    intro i t
    dsimp [L]
    split_ifs
    · exact inv_nonneg.mpr (by positivity)
    · exact norm_nonneg _
  have hL : ∀ i, ContinuousOn (L i) (Icc (-R) R) := by
    intro i
    dsimp [L]
    split_ifs
    · exact (reciprocal_abs_continuous hε).continuousOn
    · exact allBranchExterior_arclength_continuousOn B ε R hε hεr hRB
  have hLint : ∀ i, (∫ t in Icc (-R) R, L i t) ≤ C i := by
    intro i
    dsimp [L,C]
    split_ifs
    · have hh := reciprocal_abs_symmetric_integral hR hε
      rw [intervalIntegral.integral_of_le (show -R ≤ R by linarith),← integral_Icc_eq_integral_Ioc] at hh
      exact hh.le
    · exact (B.length_restrict ε hε hεr (Icc (-R) R) (by
        intro t ht
        constructor <;> linarith [ht.1,ht.2])).2
  have hv : v ∈ Finset.univ.erase p := Finset.mem_erase.mpr ⟨hpv.symm,Finset.mem_univ v⟩
  have hprod (u : Fin N → ℝ) : (∏ i ∈ Finset.univ.erase p, L i (u i)) =
      (|u v|+ε)⁻¹*(∏ i ∈ (Finset.univ.erase p).erase v, ‖deriv (originalPhase d ε) (u i)‖) := by
    rw [← Finset.mul_prod_erase (Finset.univ.erase p) (fun i => L i (u i)) hv]
    dsimp only [L]
    simp only [ite_true]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    simp [(Finset.mem_erase.mp hi).1]
  have hCprod : (∏ i ∈ Finset.univ.erase p, C i)=2*Real.log ((R+ε)/ε)*B.lengthC^(N-2) := by
    rw [← Finset.mul_prod_erase (Finset.univ.erase p) C hv]
    dsimp only [C]
    simp only [ite_true]
    congr 1
    have hh : (∏ i ∈ (Finset.univ.erase p).erase v,
        if i=v then 2*Real.log ((R+ε)/ε) else B.lengthC)=∏ _i ∈ (Finset.univ.erase p).erase v, B.lengthC := by
      apply Finset.prod_congr rfl
      intro i hi
      simp [(Finset.mem_erase.mp hi).1]
    rw [hh,Finset.prod_const,Finset.card_erase_of_mem hv,
      Finset.card_erase_of_mem (Finset.mem_univ p),Finset.card_univ,Fintype.card_fin]
    congr 1
  have hh := one_phase_sum_weighted_integral (b := d.thetaB) p v hpv L C hL0 hR hRπ hα hα1 hL hLint
  unfold allBranchExteriorLogPhaseKernel
  simpa only [hprod,hCprod,mul_assoc] using hh

end
end IsingBulk.Tail
