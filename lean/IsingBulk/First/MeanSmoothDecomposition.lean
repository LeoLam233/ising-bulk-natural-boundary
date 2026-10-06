import IsingBulk.First.MeanRealDomain
import IsingBulk.First.MeanRegularError

/-! Literal smooth-to-hard mean decomposition. Only the mean cutoff is removed
on its hard inner interval; any fixed shape cutoff stays outside. -/
namespace IsingBulk.First
noncomputable section
open Set Complex MeasureTheory

def smoothMeanIntegral {n : ℕ} (eta : ℝ → ℂ) (s : ℂ) (rho alpha delta : ℝ) (t : Fin n → ℝ) : ℂ :=
  ∫ x : ℝ in -2*delta..2*delta, eta x * meanLocalDensity s rho alpha t (x:ℂ)

theorem smoothMeanIntegral_eq_hard_add_edges {n : ℕ} (eta : ℝ → ℂ) (s : ℂ)
    (rho alpha delta : ℝ) (t : Fin n → ℝ) (hd : 0 < delta) (heta : Continuous eta)
    (hinner : ∀ x : ℝ, |x| ≤ delta → eta x = 1)
    (hf : ContinuousOn (fun x : ℝ => meanLocalDensity s rho alpha t (x:ℂ)) (Icc (-2*delta) (2*delta))) :
    smoothMeanIntegral eta s rho alpha delta t = hardMeanIntegral s rho alpha delta t +
      meanCutoffEdges eta s rho alpha delta t := by
  let f : ℝ → ℂ := fun x => eta x * meanLocalDensity s rho alpha t (x:ℂ)
  have hcf : ContinuousOn f (Icc (-2*delta) (2*delta)) := heta.continuousOn.mul hf
  have hleft : IntervalIntegrable f volume (-2*delta) (-delta) :=
    (hcf.mono (by intro x hx; exact ⟨hx.1,by linarith [hx.2]⟩)).intervalIntegrable_of_Icc (by linarith)
  have hmiddle : IntervalIntegrable f volume (-delta) delta :=
    (hcf.mono (by intro x hx; exact ⟨by linarith [hx.1],by linarith [hx.2]⟩)).intervalIntegrable_of_Icc (by linarith)
  have hright : IntervalIntegrable f volume delta (2*delta) :=
    (hcf.mono (by intro x hx; exact ⟨by linarith [hx.1],hx.2⟩)).intervalIntegrable_of_Icc (by linarith)
  have hadd := intervalIntegral.integral_add_adjacent_intervals (hleft.trans hmiddle) hright
  rw [← intervalIntegral.integral_add_adjacent_intervals hleft hmiddle] at hadd
  have hmid : (∫ x in -delta..delta, f x) = hardMeanIntegral s rho alpha delta t := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    dsimp [f]
    rw [hinner x (abs_le.mpr hx),one_mul]
  have heL : (∫ x in -2*delta..-delta, f x) = ∫ x in Icc (-2*delta) (-delta), f x := by
    rw [intervalIntegral.integral_of_le (by linarith),integral_Icc_eq_integral_Ioc]
  have heR : (∫ x in delta..2*delta, f x) = ∫ x in Icc delta (2*delta), f x := by
    rw [intervalIntegral.integral_of_le (by linarith),integral_Icc_eq_integral_Ioc]
  rw [hmid,heL,heR] at hadd
  change (∫ x in -2*delta..2*delta, f x) = _
  rw [← hadd]
  unfold meanCutoffEdges
  dsimp [f]
  ring

theorem smoothMeanIntegral_eq_residue_add_error {n : ℕ} (eta : ℝ → ℂ) (s : ℂ)
    (rho alpha delta : ℝ) (t : Fin n → ℝ) (hd : 0 < delta) (heta : Continuous eta)
    (hinner : ∀ x : ℝ, |x| ≤ delta → eta x = 1)
    (hf : ContinuousOn (fun x : ℝ => meanLocalDensity s rho alpha t (x:ℂ)) (Icc (-2*delta) (2*delta)))
    (hres : clockwiseRectangle delta 0 (-delta) (meanLocalDensity s rho alpha t) = postMeanDensity s alpha t) :
    smoothMeanIntegral eta s rho alpha delta t = postMeanDensity s alpha t +
      meanRegularError eta s rho alpha delta t := by
  rw [smoothMeanIntegral_eq_hard_add_edges eta s rho alpha delta t hd heta hinner hf,
    hardMean_eq_residue_add_sides s rho alpha delta delta t hres]
  simp only [meanRegularError,add_assoc]

end
end IsingBulk.First
