import IsingBulk.Joint.FormFactors.NormalizedRestriction
import IsingBulk.Joint.Transverse.PositiveObstruction
import IsingBulk.Joint.Transverse.NegativeEvenObstruction
import IsingBulk.Anisotropic.RegularEdges.PositiveEndpointHigh

namespace IsingBulk.Joint
noncomputable section
open Set IsingBulk.Anisotropic

@[fun_prop] theorem ratioSlice_continuous (lam : ℝ) : Continuous (ratioSlice lam) := by
  unfold ratioSlice
  fun_prop

theorem ratioSlice_high_frontier {lam : ℝ} (hlam : 0 < lam) {z : ℂ}
    (hz : z ∈ frontier (omegaH lam)) : ratioSlice lam z ∈ frontier highDomain := by
  have h := (ratioSlice_continuous lam).frontier_preimage_subset highDomain
  rw [highDomain_pullback hlam] at h
  exact h hz

theorem ratioSlice_low_frontier {lam : ℝ} (hlam : 0 < lam) {z : ℂ}
    (hz : z ∈ frontier (omegaL lam)) : ratioSlice lam z ∈ frontier lowDomain := by
  have h := (ratioSlice_continuous lam).frontier_preimage_subset lowDomain
  rw [lowDomain_pullback hlam] at h
  exact h hz

theorem transferB_ratio_im (lam : ℝ) (z : ℂ) :
    (transferB (ratioSlice lam z)).im = Anisotropic.spectralDet lam z / Complex.normSq (spectralS z) := by
  simp only [transferB,T_ratioSlice,S_ratioSlice,Complex.div_im,Anisotropic.spectralDet]
  ring

theorem transfer_edge_ratio (lam : ℝ) (eps : ℂ) (z : ℂ) :
    transferC (ratioSlice lam z)-eps*transferB (ratioSlice lam z) = edgeMapV lam eps z := by
  simp only [transferC,transferB,A_ratioSlice,S_ratioSlice,T_ratioSlice,edgeMapV]
  ring

theorem positiveParameter_ratio (lam b : ℝ) (z : ℂ) :
    Transverse.positiveParameter b (ratioSlice lam z) = edgeMapV lam 1 z-(b:ℂ) := by
  unfold Transverse.positiveParameter
  simpa using congrArg (fun v : ℂ => v-(b:ℂ)) (transfer_edge_ratio lam 1 z)

theorem negativeParameter_ratio (lam b : ℝ) (z : ℂ) :
    Transverse.negativeParameter b (ratioSlice lam z) = edgeMapV lam (-1) z-(b:ℂ) := by
  unfold Transverse.negativeParameter
  simpa using congrArg (fun v : ℂ => v-(b:ℂ)) (transfer_edge_ratio lam (-1) z)

end
end IsingBulk.Joint
