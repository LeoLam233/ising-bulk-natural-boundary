import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic

/-! Exact periodic weighted two-angle estimate for the original-contour
Pfaffian matching bound. The proof uses 2ab≤a²+b² and genuine Fubini. -/
namespace IsingBulk.Tail
noncomputable section
open MeasureTheory Set
open scoped Topology

theorem periodic_kernel_integral_translate {T : ℝ} (hT : 0 ≤ T) {K : ℝ → ℝ}
    (hK : Function.Periodic K T) (a : ℝ) :
    (∫ y in Icc (0:ℝ) T, K (a+y)) = ∫ y in Icc (0:ℝ) T, K y := by
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hT,
    intervalIntegral.integral_comp_add_left]
  simp only [add_zero]
  rw [hK.intervalIntegral_add_eq a 0,zero_add,
    intervalIntegral.integral_of_le hT,← integral_Icc_eq_integral_Ioc]

theorem weighted_periodic_pair_integral_le {T : ℝ} (hT : 0 ≤ T)
    {R K : ℝ → ℝ} (hR : Continuous R) (hK : Continuous K)
    (hperiod : Function.Periodic K T) (hKpos : ∀ x : ℝ, 0 ≤ K x) :
    (∫ p in Icc (0:ℝ) T ×ˢ Icc (0:ℝ) T, R p.1*R p.2*K (p.1+p.2)) ≤
      (∫ x in Icc (0:ℝ) T, R x^2)*(∫ y in Icc (0:ℝ) T, K y) := by
  let B := Icc (0:ℝ) T
  let F : ℝ × ℝ → ℝ := fun p => R p.1*R p.2*K (p.1+p.2)
  let G : ℝ × ℝ → ℝ := fun p => R p.1^2*K (p.1+p.2)
  let H : ℝ × ℝ → ℝ := fun p => R p.2^2*K (p.1+p.2)
  have hFc : Continuous F := ((hR.comp continuous_fst).mul (hR.comp continuous_snd)).mul
    (hK.comp (continuous_fst.add continuous_snd))
  have hGc : Continuous G := ((hR.comp continuous_fst).pow 2).mul
    (hK.comp (continuous_fst.add continuous_snd))
  have hHc : Continuous H := ((hR.comp continuous_snd).pow 2).mul
    (hK.comp (continuous_fst.add continuous_snd))
  have hFi : IntegrableOn F (B ×ˢ B) := hFc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hGi : IntegrableOn G (B ×ˢ B) := hGc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hHi : IntegrableOn H (B ×ˢ B) := hHc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hinner (x : ℝ) : (∫ y in B, G (x,y)) = R x^2*(∫ y in B, K y) := by
    change (∫ y in B, R x^2*K (x+y)) = _
    rw [integral_const_mul]
    congr 1
    exact periodic_kernel_integral_translate hT hperiod x
  have hGEq : (∫ p in B ×ˢ B, G p) =
      (∫ x in B, R x^2)*(∫ y in B, K y) := by
    rw [Measure.volume_eq_prod, setIntegral_prod G (by rwa [← Measure.volume_eq_prod])]
    simp_rw [hinner]
    rw [integral_mul_const]
  have hHEq : (∫ p in B ×ˢ B, H p) =
      (∫ x in B, R x^2)*(∫ y in B, K y) := by
    have he : H = fun p => G p.swap := by
      funext p
      dsimp only [G,H,Prod.swap]
      rw [add_comm]
    rw [he,Measure.volume_eq_prod,setIntegral_prod_swap,← Measure.volume_eq_prod,hGEq]
  have hbound : (∫ p in B ×ˢ B, F p) ≤ ∫ p in B ×ˢ B, (G p+H p)/2 := by
    apply setIntegral_mono_on hFi ((hGi.add hHi).div_const 2)
      (measurableSet_Icc.prod measurableSet_Icc)
    intro p hp
    dsimp only [F,G,H,Pi.add_apply]
    have h := mul_nonneg (sq_nonneg (R p.1-R p.2)) (hKpos (p.1+p.2))
    nlinarith
  calc
    _ ≤ ∫ p in B ×ˢ B, (G p+H p)/2 := hbound
    _ = ((∫ p in B ×ˢ B, G p)+(∫ p in B ×ˢ B, H p))/2 := by
      rw [integral_div,integral_add hGi hHi]
    _ = _ := by rw [hGEq,hHEq]; ring

end
end IsingBulk.Tail
