import IsingBulk.Tail.UltraHighDerivatives
import IsingBulk.Tail.UltraHighFactorialTail
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Filter Asymptotics Set
open scoped Topology

theorem log_inverse_tendsto_atTop :
    Tendsto (fun e : ℝ => Real.log (1/e)) (𝓝[>] 0) atTop := by
  simpa only [one_div,Real.log_inv,Function.comp_def] using (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero)

theorem ultraHighFactorialTail_weighted_littleO {D L : ℝ} (hD : 0 ≤ D)
    (hL : 1 ≤ L) (hLD : 2*D*Real.exp 1 ≤ L) (b A : ℝ) :
    (fun H : ℝ => Real.exp (b*H)*ultraHighFactorialTail D L H) =o[atTop]
      (fun H : ℝ => Real.exp (-A*H)) := by
  have hh := (ultraHighFactorialTail_littleO hD hL hLD (A+b)).mul_isBigO
    (Asymptotics.isBigO_refl (fun H : ℝ => Real.exp (b*H)) atTop)
  apply hh.congr' (Eventually.of_forall (fun H => by ring))
  apply Eventually.of_forall
  intro H
  dsimp only
  rw [← Real.exp_add]
  congr 1
  ring

theorem ultraHighFactorialTail_radial_littleO {D L : ℝ} (hD : 0 ≤ D)
    (hL : 1 ≤ L) (hLD : 2*D*Real.exp 1 ≤ L) (b A : ℝ) :
    (fun e : ℝ => Real.exp (b*Real.log (1/e))*
      ultraHighFactorialTail D L (Real.log (1/e))) =o[𝓝[>] 0]
        (fun e : ℝ => e^A) := by
  have hh := (ultraHighFactorialTail_weighted_littleO hD hL hLD b A).comp_tendsto
    log_inverse_tendsto_atTop
  apply hh.congr' (Eventually.of_forall (fun _ => rfl))
  filter_upwards [self_mem_nhdsWithin] with e he
  rw [Real.rpow_def_of_pos he]
  simp only [Function.comp_def,one_div,Real.log_inv]
  congr 1
  ring

end
end IsingBulk.Tail
