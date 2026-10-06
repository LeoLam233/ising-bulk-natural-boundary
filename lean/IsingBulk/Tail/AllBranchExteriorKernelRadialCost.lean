import IsingBulk.Tail.AllBranchExteriorNearKernelMajorant

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch

theorem allBranchExterior_radial_log_factor (κ H : ℝ) (hκ : 0 < κ) (hH : 0 ≤ H) :
    1+|Real.log (κ*Real.exp (-H))| ≤ (1+|Real.log κ|)*(H+1) := by
  rw [Real.log_mul hκ.ne' (Real.exp_pos _).ne',Real.log_exp]
  have hh := abs_add_le (Real.log κ) (-H)
  rw [abs_neg,abs_of_nonneg hH] at hh
  nlinarith [abs_nonneg (Real.log κ)]

def allBranchExteriorRadialLogConstant : ℝ := 1+(Real.log 2)⁻¹

theorem allBranchExterior_radial_ratio_log (R H : ℝ) (hR : 0 ≤ R) (hR1 : R ≤ 1) (hH : 0 ≤ H) :
    Real.log ((R+Real.exp (-H))/Real.exp (-H)) ≤
      allBranchExteriorRadialLogConstant*Real.log 2*(H+1) := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he : Real.exp (-H) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hsum : 0 < R+Real.exp (-H) := by positivity
  have hl : Real.log (R+Real.exp (-H)) ≤ Real.log 2 := Real.log_le_log hsum (by linarith)
  rw [Real.log_div hsum.ne' (Real.exp_pos _).ne',Real.log_exp]
  have hc : allBranchExteriorRadialLogConstant*Real.log 2=Real.log 2+1 := by
    unfold allBranchExteriorRadialLogConstant
    rw [add_mul,one_mul,inv_mul_cancel₀ hL.ne']
  rw [hc]
  nlinarith

theorem allBranchExterior_negative_cost_radial {d : LocalBranchData} (B : BranchEstimates d)
    (R a c C H : ℝ) (N : ℕ) (hR : 0 ≤ R) (hR1 : R ≤ 1)
    (ha : 0 < a) (hc : 0 < c) (hC : 0 ≤ C) (hH : 0 ≤ H) :
    allBranchExteriorNegativeCost B (Real.exp (-H)) R a c C N ≤
      allBranchExteriorRadialLogConstant*allBranchExteriorNegativeCost B 1 1 a c C N*(H+1)^2 := by
  let T := allBranchExteriorRadialLogConstant
  let L := 1+|Real.log d.c₀|
  let S := H+1
  let A := 2*(B.magnitudeUpper/Real.sqrt a)/(c*Real.sqrt a)
  let D := 2*(B.magnitudeUpper/Real.sqrt a)*C
  let X := A*((N:ℝ)*simpleKernelConstant*L*B.lengthC^(N-1))
  let Y := (N:ℝ)*(D*((N:ℝ)*simpleKernelConstant*L)*(2*Real.log 2)*B.lengthC^(N-2))
  have hmag := B.magnitudeUpper_pos
  have hlen := B.lengthC_pos
  have hsk := simpleKernelConstant_pos
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hT : 1 ≤ T := by
    dsimp [T,allBranchExteriorRadialLogConstant]
    exact le_add_of_nonneg_right (inv_nonneg.mpr hlog.le)
  have hS : 1 ≤ S := by dsimp [S]; linarith
  have hX : 0 ≤ X := by dsimp [X,A,L]; positivity
  have hY : 0 ≤ Y := by dsimp [Y,D,L]; positivity
  have hkernel := allBranchExterior_radial_log_factor d.c₀ H d.c₀_pos hH
  have hratio := allBranchExterior_radial_ratio_log R H hR hR1 hH
  have hratio0 : 0 ≤ Real.log ((R+Real.exp (-H))/Real.exp (-H)) :=
    Real.log_nonneg ((one_le_div (Real.exp_pos _)).mpr (by linarith))
  have hb : allBranchExteriorNegativeCost B (Real.exp (-H)) R a c C N ≤ X*S+T*Y*S^2 := by
    unfold allBranchExteriorNegativeCost
    calc
      _ ≤ A*(((N:ℝ)*simpleKernelConstant*(L*S))*B.lengthC^(N-1))+
          (N:ℝ)*(D*(((N:ℝ)*simpleKernelConstant*(L*S))*(2*(T*Real.log 2*S))*B.lengthC^(N-2))) := by
        dsimp [A,D,L,S,T]
        gcongr
      _ = _ := by dsimp [X,Y]; ring
  have he : allBranchExteriorNegativeCost B 1 1 a c C N=X+Y := by
    simp only [allBranchExteriorNegativeCost,mul_one,show (1:ℝ)+1=2 by norm_num,div_one]
    dsimp [X,Y,A,D,L]
    ring
  rw [he]
  apply hb.trans
  have hs2 : S ≤ S^2 := by nlinarith
  have hfirst : X*S ≤ T*X*S^2 := by
    calc
      _ ≤ X*S^2 := mul_le_mul_of_nonneg_left hs2 hX
      _ ≤ T*(X*S^2) := le_mul_of_one_le_left (mul_nonneg hX (sq_nonneg S)) hT
      _ = _ := by ring
  change X*S+T*Y*S^2 ≤ T*(X+Y)*S^2
  nlinarith

theorem allBranchExterior_near_kernel_cost_radial {d : LocalBranchData} (B : BranchEstimates d)
    (R a D ζ c C H : ℝ) (N Q : ℕ) (hR : 0 ≤ R) (hR1 : R ≤ 1)
    (ha : 0 < a) (hD : 0 < D) (hζ : 0 < ζ) (hc : 0 < c) (hC : 0 ≤ C) (hH : 0 ≤ H) :
    allBranchExteriorNearKernelCost B (Real.exp (-H)) R a D ζ c C N Q ≤
      allBranchExteriorRadialLogConstant*allBranchExteriorNearKernelCost B 1 1 a D ζ c C N Q*(H+1)^2 := by
  let P := 4*((N:ℝ)^2*((D^Q*allBranchExteriorPositiveCost B a D)*
    (((N:ℝ)*simpleKernelConstant*(1+|Real.log d.c₀|))*
      ((N:ℝ)*simpleKernelConstant*(1+|Real.log ζ|))*B.lengthC^(N-2))))
  have hP : 0 ≤ P := by
    have hpc := allBranchExterior_positive_cost_nonneg B ha hD
    have hsk := simpleKernelConstant_pos
    have hlen := B.lengthC_pos
    dsimp [P]
    positivity
  have hp : 4*((N:ℝ)^2*((D^Q*allBranchExteriorPositiveCost B a D)*
      (((N:ℝ)*simpleKernelConstant*(1+|Real.log (d.c₀*Real.exp (-H))|))*
        ((N:ℝ)*simpleKernelConstant*(1+|Real.log (ζ*Real.exp (-H))|))*B.lengthC^(N-2)))) ≤ P*(H+1)^2 := by
    have hpc := allBranchExterior_positive_cost_nonneg B ha hD
    have hsk := simpleKernelConstant_pos
    have hlen := B.lengthC_pos
    have hlog₁ := allBranchExterior_radial_log_factor d.c₀ H d.c₀_pos hH
    have hlog₂ := allBranchExterior_radial_log_factor ζ H hζ hH
    calc
      _ ≤ 4*((N:ℝ)^2*((D^Q*allBranchExteriorPositiveCost B a D)*
          (((N:ℝ)*simpleKernelConstant*((1+|Real.log d.c₀|)*(H+1)))*
            ((N:ℝ)*simpleKernelConstant*((1+|Real.log ζ|)*(H+1)))*B.lengthC^(N-2)))) := by gcongr
      _ = _ := by dsimp [P]; ring
  have hT : 1 ≤ allBranchExteriorRadialLogConstant := by
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    unfold allBranchExteriorRadialLogConstant
    exact le_add_of_nonneg_right (inv_nonneg.mpr hlog.le)
  have hn := allBranchExterior_negative_cost_radial B R a c C H N hR hR1 ha hc hC hH
  unfold allBranchExteriorNearKernelCost
  simp only [mul_one]
  apply (add_le_add hp (mul_le_mul_of_nonneg_left hn (pow_nonneg hD.le Q))).trans
  change P*(H+1)^2+D^Q*(allBranchExteriorRadialLogConstant*allBranchExteriorNegativeCost B 1 1 a c C N*(H+1)^2) ≤
    allBranchExteriorRadialLogConstant*(P+D^Q*allBranchExteriorNegativeCost B 1 1 a c C N)*(H+1)^2
  nlinarith [mul_le_mul_of_nonneg_right hT (mul_nonneg hP (sq_nonneg (H+1)))]

end
end IsingBulk.Tail
