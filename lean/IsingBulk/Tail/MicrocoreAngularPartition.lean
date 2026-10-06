import IsingBulk.Tail.AngularFinitePartition
import IsingBulk.Tail.AllBranchExteriorCutoffs
import IsingBulk.Tail.SectorMicrocoreAngleBox
import IsingBulk.Tail.SectorIntegralDecomposition

/-! Literal angleBox all-branch micro/near/far decomposition, with real
weights fixed before every complex-parameter derivative. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch MeasureTheory Set
open scoped BigOperators Topology ContDiff

def microPartitionWeight {N : ℕ} (a rho : ℝ) (label : Option (Fin N × Fin 2))
    (u : Fin N → ℝ) : ℝ :=
  match label with
  | none => scaledMicroCutoff N a u
  | some (q,k) => if k=0 then microExteriorNearWeight a rho q u else microExteriorFarWeight a rho q u

theorem microPartitionWeight_sum {N : ℕ} (a rho : ℝ) (u : Fin N → ℝ) :
    ∑ label : Option (Fin N × Fin 2), microPartitionWeight a rho label u = 1 := by
  rw [Fintype.sum_option,Fintype.sum_prod_type]
  simp only [microPartitionWeight,Fin.sum_univ_two,ite_true,show (1:Fin 2) ≠ 0 by decide,ite_false]
  exact microExterior_full_partition a rho u

theorem microPartitionWeight_smooth {N : ℕ} (a rho : ℝ) (label : Option (Fin N × Fin 2)) :
    ContDiff ℝ ∞ (microPartitionWeight a rho label) := by
  cases label with
  | none => exact scaledMicroCutoff_smooth N a
  | some label =>
    by_cases hk : label.2=0
    · change ContDiff ℝ ∞ (fun u => if label.2=0 then microExteriorNearWeight a rho label.1 u else microExteriorFarWeight a rho label.1 u)
      simp only [hk,ite_true]
      exact (microExteriorAnchor_smooth a label.1).mul (branch_shape_cutoffs_smooth rho).2
    · change ContDiff ℝ ∞ (fun u => if label.2=0 then microExteriorNearWeight a rho label.1 u else microExteriorFarWeight a rho label.1 u)
      simp only [hk,ite_false]
      exact (microExteriorAnchor_smooth a label.1).mul (branch_shape_cutoffs_smooth rho).1

def allBranchAngularWeight {N : ℕ} (f : SelectorFunctions) (b delta : ℝ) (hd : 0 < delta)
    (theta : Fin N → ℝ) : ℂ :=
  (angularSelector f theta:ℂ)*(∏ i, sectorBranch b delta hd (theta i):ℝ)

def microPartitionAngularIntegral (N : ℕ) (f : SelectorFunctions) (r tau b delta : ℝ)
    (hd : 0 < delta) (a rho : ℝ) (label : Option (Fin N × Fin 2)) : ℂ → ℂ :=
  weightedAngularIntegral N f r tau 0 (fun theta => allBranchAngularWeight f b delta hd theta *
    (microPartitionWeight a rho label (fun i => theta i+b-2*Real.pi):ℝ))

theorem allBranchAngularWeight_continuous {N : ℕ} (f : SelectorFunctions) (hf : RegularSelector f)
    (b delta : ℝ) (hd : 0 < delta) : Continuous (@allBranchAngularWeight N f b delta hd) := by
  apply (complexSelector_contDiff f hf).continuous.mul
  apply Complex.continuous_ofReal.comp
  exact (contDiff_prod (fun i _ => (sector_labels_smooth b delta hd).2.2.comp
    (contDiff_apply ℝ ℝ i))).continuous

theorem all_branch_micro_partition_derivative (N : ℕ) (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r tau : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (htau : 0 ≤ tau)
    (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner) (a rho : ℝ)
    (s : ℂ) (hs : s ∈ dampingDomain r) (j : ℕ) :
    iteratedDeriv j (originalSectorIntegral N f r tau b outer inner ho hi none) s =
      ∑ label : Option (Fin N × Fin 2),
        iteratedDeriv j (microPartitionAngularIntegral N f r tau b outer ho a rho label) s := by
  have hmap : Continuous (fun theta : Fin N → ℝ => fun i => theta i+b-2*Real.pi) := by fun_prop
  apply weightedAngularIntegral_finite_partition_jets N hN f hf hr hr1 htau le_rfl
    (allBranchAngularWeight f b outer ho) (allBranchAngularWeight_continuous f hf b outer ho)
    (fun label theta => (microPartitionWeight a rho label (fun i => theta i+b-2*Real.pi):ℝ))
  · intro label
    exact Complex.continuous_ofReal.comp ((microPartitionWeight_smooth a rho label).continuous.comp hmap)
  · intro theta
    rw [← Complex.ofReal_sum,microPartitionWeight_sum,Complex.ofReal_one]
  · exact hs

theorem microPartitionAngularIntegral_none (n : ℕ) (d : LocalBranchData)
    (eta delta : ℝ) (hd : 0 < delta) (eps a rho : ℝ) :
    microPartitionAngularIntegral (n+2) (constructedSelector d.thetaB eta d.alpha)
      (Real.exp (-d.c₀*eps)) d.tau d.thetaB delta hd a rho none =
        angleBoxMicrocoreIntegral n d eta delta hd eps a := by
  funext s
  apply setIntegral_congr_fun measurableSet_Icc
  intro theta _
  dsimp [microPartitionAngularIntegral,weightedAngularIntegral,allBranchAngularWeight,
    microPartitionWeight,angleBoxMicrocoreIntegral]
  push_cast
  ring

end
end IsingBulk.Tail
