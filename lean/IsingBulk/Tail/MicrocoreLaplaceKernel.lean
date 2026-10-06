import IsingBulk.Analysis.BranchLength

/-! Explicit real-variable Laplace bound for the square-root branch length
majorant. This avoids treating a coupled occupancy as a Fubini parameter. -/
namespace IsingBulk.Tail
noncomputable section
open MeasureTheory Set

 def sqrtLaplaceKernel (a ε u : ℝ) : ℝ :=
  Real.exp (-a*Real.sqrt (|u|+ε))/Real.sqrt (|u|+ε)

 theorem sqrtLaplaceKernel_continuous (a ε : ℝ) (hε : 0 < ε) :
    Continuous (sqrtLaplaceKernel a ε) := by
  unfold sqrtLaplaceKernel
  fun_prop (disch := intro u; exact (Real.sqrt_pos.mpr (by positivity : 0 < |u|+ε)).ne')

 theorem sqrt_laplace_integral (a ε r : ℝ) (ha : 0 < a) (hε : 0 < ε) (hr : 0 ≤ r) :
    (∫ u in -r..r, sqrtLaplaceKernel a ε u) ≤ 4/a := by
  let f := sqrtLaplaceKernel a ε
  have hfc := sqrtLaplaceKernel_continuous a ε hε
  have hpositive : (∫ u in 0..r, f u) =
      (2/a)*(Real.exp (-a*Real.sqrt ε)-Real.exp (-a*Real.sqrt (r+ε))) := by
    have hi : IntervalIntegrable (fun u : ℝ => Real.exp (-a*Real.sqrt (u+ε))/Real.sqrt (u+ε)) volume 0 r := by
      apply ContinuousOn.intervalIntegrable
      intro u hu
      have hu0 : 0 ≤ u := (uIcc_of_le hr ▸ hu).1
      apply ContinuousAt.continuousWithinAt
      fun_prop (disch := positivity)
    have hd : ∀ u ∈ uIcc (0:ℝ) r,
      HasDerivAt (fun v : ℝ => (-2/a)*Real.exp (-a*Real.sqrt (v+ε)))
        (Real.exp (-a*Real.sqrt (u+ε))/Real.sqrt (u+ε)) u := by
      intro u hu
      have hu0 : 0 ≤ u := (uIcc_of_le hr ▸ hu).1
      have hs : 0 < u+ε := by positivity
      have hh := (((((hasDerivAt_id u).add_const ε).sqrt hs.ne').const_mul (-a)).exp).const_mul (-2/a)
      convert! hh using 1
      dsimp
      field_simp [ha.ne', (Real.sqrt_pos.mpr hs).ne']
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
    have hf : (∫ u in 0..r, f u) =
        ∫ u in 0..r, Real.exp (-a*Real.sqrt (u+ε))/Real.sqrt (u+ε) := by
      apply intervalIntegral.integral_congr
      intro u hu
      have hu0 : 0 ≤ u := (uIcc_of_le hr ▸ hu).1
      simp [f,sqrtLaplaceKernel,abs_of_nonneg hu0]
    rw [hf,he]
    simp
    ring
  have hnegative : (∫ u in -r..0, f u)=∫ u in 0..r, f u := by
    simpa [f,sqrtLaplaceKernel,abs_neg] using
      (intervalIntegral.integral_comp_neg (f := f) (a := 0) (b := r)).symm
  have hsplit : (∫ u in -r..0, f u)+(∫ u in 0..r, f u)=∫ u in -r..r, f u :=
    intervalIntegral.integral_add_adjacent_intervals
    (hfc.intervalIntegrable (-r) 0) (hfc.intervalIntegrable 0 r)
  change (∫ u in -r..r, f u) ≤ _
  rw [← hsplit,hnegative,hpositive]
  have he1 : Real.exp (-a*Real.sqrt ε) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [Real.sqrt_nonneg ε])
  have he0 : 0 ≤ Real.exp (-a*Real.sqrt (r+ε)) := (Real.exp_pos _).le
  have hfactor : 0 ≤ 2/a := by positivity
  have hh := mul_le_mul_of_nonneg_left (show Real.exp (-a*Real.sqrt ε)-Real.exp (-a*Real.sqrt (r+ε)) ≤ 1 by linarith) hfactor
  have hh' := add_le_add hh hh
  simp only [mul_one] at hh'
  convert! hh' using 1
  ring

end
end IsingBulk.Tail
