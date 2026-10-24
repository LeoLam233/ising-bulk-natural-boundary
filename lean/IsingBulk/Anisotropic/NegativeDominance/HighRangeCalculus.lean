import IsingBulk.Anisotropic.NegativeDominance.ExactModel
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
set_option maxHeartbeats 800000

/-- The all-index large-particle exponent decreases fast enough already at
N² ≥ j/√log j, exactly the manuscript's intermediate/high cutoff. -/
theorem high_range_exponent_bound (j N C : ℝ) (hj : 0<j) (hN : 1≤N)
    (hL : 1024≤Real.log j) (hC : 32*C≤Real.log j)
    (hcut : j/Real.sqrt (Real.log j)≤N^2) :
    2*j*Real.log N-N^2/2*Real.log N+C*N^2≤
      j*Real.log j-j*Real.sqrt (Real.log j)/32-N := by
  let L := Real.log j
  have hLp : 0<L := by dsimp [L]; linarith
  have hs : 0<Real.sqrt L := Real.sqrt_pos.mpr hLp
  have hs2 : (Real.sqrt L)^2=L := Real.sq_sqrt hLp.le
  have hs32 : 32≤Real.sqrt L := by
    have hh : Real.sqrt 1024≤Real.sqrt L := Real.sqrt_le_sqrt hL
    norm_num at hh
    exact hh
  have hsc : Real.sqrt L+C≤L/16 := by
    have hh : 32*Real.sqrt L≤L := by nlinarith only [hs2,hs32]
    change 32*C≤L at hC
    linarith
  let a := j/Real.sqrt L
  have ha : 0<a := div_pos hj hs
  have hNp : 0<N := lt_of_lt_of_le zero_lt_one hN
  have hxp : 0<N^2 := sq_pos_of_pos hNp
  have hla : Real.log a=L-Real.log L/2 := by
    rw [Real.log_div hj.ne' hs.ne',Real.log_sqrt hLp.le]
  have hlaLo : L/2≤Real.log a := by
    have hh := Real.log_le_sub_one_of_pos hLp
    rw [hla]
    linarith
  have hlaHi : Real.log a≤L := by
    rw [hla]
    have hh : 0≤Real.log L := Real.log_nonneg (by dsimp [L]; linarith)
    linarith
  have hlog : Real.log (N^2)-Real.log a≤N^2/a-1 := by
    have hh := Real.log_le_sub_one_of_pos (div_pos hxp ha)
    simpa only [Real.log_div hxp.ne' ha.ne'] using hh
  have hratio : j*(N^2/a-1)=Real.sqrt L*N^2-j := by
    dsimp [a]
    field_simp
  have hjlog : j*Real.log (N^2)≤j*L+Real.sqrt L*N^2-j := by
    have hh := mul_le_mul_of_nonneg_left hlog hj.le
    rw [hratio] at hh
    have hh' := mul_le_mul_of_nonneg_left hlaHi hj.le
    nlinarith only [hh,hh']
  have hlogLo : L/2≤Real.log (N^2) :=
    hlaLo.trans (Real.log_le_log ha hcut)
  have hneg := mul_le_mul_of_nonneg_left hlogLo (show 0≤N^2/4 by positivity)
  have hscx := mul_le_mul_of_nonneg_right hsc (sq_nonneg N)
  have hmain : j*Real.log (N^2)-N^2/4*Real.log (N^2)+C*N^2≤j*L-L*N^2/16 := by
    nlinarith only [hjlog,hneg,hscx,hj.le]
  have hcut' : j*Real.sqrt L≤L*N^2 := by
    have hh := (div_le_iff₀ hs).mp hcut
    have hh' := mul_le_mul_of_nonneg_right hh hs.le
    nlinarith only [hh',hs2]
  have hdec : 32*N≤L*N^2 := by
    have hL32 : 32≤L := by dsimp [L]; linarith
    have hh := mul_le_mul_of_nonneg_right hL32 (sq_nonneg N)
    nlinarith only [hh,hN]
  rw [Real.log_pow] at hmain
  change _ ≤j*L-j*Real.sqrt L/32-N
  nlinarith only [hmain,hcut',hdec]

end
end IsingBulk.Anisotropic.NegativeDominance
