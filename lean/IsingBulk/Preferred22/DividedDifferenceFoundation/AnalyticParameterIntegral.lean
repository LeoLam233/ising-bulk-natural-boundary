/-
Copyright (c) 2026 Dehao Lin. Released under the MIT License.
See LICENSE-LT.txt in DividedDifferenceFoundation for the full license.
Adapted only by namespace/import relocation from the pinned LT repository
commit 43a9ce897ba12de0c96d6e1a636790cd93fae8ff.
Exact source hashes and adaptation scope: PROVENANCE.json.
-/
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic

/-! Analytic integration of a uniformly contracting linear family, proved by
integrating the actual convergent multilinear power series coefficient by coefficient. -/
namespace IsingBulk.Preferred22.DividedDifferenceFoundation
noncomputable section
open scoped Topology BigOperators
open Set MeasureTheory

private theorem norm_integral_unit_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (C : ℝ) (h : ∀ s ∈ Icc (0:ℝ) 1, ‖f s‖ ≤ C) :
    ‖∫ s in Icc (0:ℝ) 1, f s‖ ≤ C := by
  simpa only [Real.volume_real_Icc_of_le zero_le_one,sub_zero,mul_one] using
    norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure ℝ)) (isCompact_Icc.measure_lt_top) h

theorem analyticAt_integral_linear_contractions
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (f : E → F) (hf : AnalyticAt ℂ f 0) (A : ℝ → E →L[ℂ] E)
    (hA : Continuous A) (hbound : ∀ s ∈ Icc (0:ℝ) 1, ‖A s‖ ≤ 1) :
    AnalyticAt ℂ (fun x => ∫ s in Icc (0:ℝ) 1, f (A s x)) 0 := by
  obtain ⟨p,R,hp⟩ := hf
  obtain ⟨r,hr0,hrR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.r_pos
  let b (n : ℕ) (s : ℝ) := p.compContinuousLinearMap (A s) n
  let q : FormalMultilinearSeries ℂ E F := fun n => ∫ s in Icc (0:ℝ) 1, b n s
  have hbcont (n : ℕ) : Continuous (b n) := by
    exact (ContinuousMultilinearMap.compContinuousLinearMapLRight (E := fun _ : Fin n => E) (p n)).cont.comp
      (continuous_pi (fun _ => hA))
  have hbint (n : ℕ) : IntegrableOn (b n) (Icc (0:ℝ) 1) :=
    (hbcont n).continuousOn.integrableOn_compact isCompact_Icc
  have hbnorm (n : ℕ) (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : ‖b n s‖ ≤ ‖p n‖ := by
    calc
      _ ≤ ‖p n‖*‖A s‖^n := p.norm_compContinuousLinearMap_le (A s) n
      _ ≤ ‖p n‖*1^n := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hbound s hs) n) (norm_nonneg _)
      _ = _ := by simp
  have hqnorm (n : ℕ) : ‖q n‖ ≤ ‖p n‖ := norm_integral_unit_le (b n) _ (hbnorm n)
  have hpr : (r:ENNReal)<p.radius := hrR.trans_le hp.r_le
  have hqr : (r:ENNReal) ≤ q.radius := q.le_radius_of_summable
    (Summable.of_nonneg_of_le (fun n => by positivity)
      (fun n => mul_le_mul_of_nonneg_right (hqnorm n) (by positivity)) (p.summable_norm_mul_pow hpr))
  refine ⟨q,r,hqr,hr0,?_⟩
  intro y hy
  have hy' : (‖y‖₊:ENNReal)<r := mem_eball_zero_iff.mp hy
  have hseries := p.summable_norm_mul_pow (hy'.trans hpr)
  let G (n : ℕ) (s : ℝ) := b n s (fun _ => y)
  have hGint (n : ℕ) : IntegrableOn (G n) (Icc (0:ℝ) 1) :=
    ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin n => E) F (fun _ => y)).integrable_comp (hbint n))
  have hGnorm (n : ℕ) (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : ‖G n s‖ ≤ ‖p n‖*‖y‖^n := by
    calc
      _ ≤ ‖b n s‖*∏ _i : Fin n, ‖y‖ := (b n s).le_opNorm _
      _ = ‖b n s‖*‖y‖^n := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (hbnorm n s hs) (by positivity)
  have hsumInt : Summable (fun n => ∫ s in Icc (0:ℝ) 1, ‖G n s‖) := by
    apply Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _)) _ hseries
    intro n
    rw [← Real.norm_of_nonneg (integral_nonneg (fun s => norm_nonneg (G n s)))]
    exact norm_integral_unit_le (fun s => ‖G n s‖) _ (fun s hs => by simpa only [norm_norm,coe_nnnorm] using hGnorm n s hs)
  have hsum := hasSum_integral_of_summable_integral_norm hGint hsumInt
  have heq (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : (∑' n, G n s)=f (A s y) := by
    have hay : ‖A s y‖ ≤ ‖y‖ := (A s).le_opNorm y |>.trans (by
      simpa using mul_le_mul_of_nonneg_right (hbound s hs) (norm_nonneg y))
    have hay' : (‖A s y‖₊:ENNReal) ≤ ‖y‖₊ := by exact_mod_cast hay
    have hball : A s y ∈ Metric.eball (0:E) R := mem_eball_zero_iff.mpr (hay'.trans_lt (hy'.trans hrR))
    simpa only [G,b,FormalMultilinearSeries.compContinuousLinearMap,
      ContinuousMultilinearMap.compContinuousLinearMap_apply,zero_add] using (hp.hasSum hball).tsum_eq
  have hcoeff (n : ℕ) : q n (fun _ => y)=∫ s in Icc (0:ℝ) 1, G n s :=
    ContinuousMultilinearMap.integral_apply (hbint n) (fun _ => y)
  simp only [zero_add]
  rw [show (fun n => q n (fun _ => y))=(fun n => ∫ s in Icc (0:ℝ) 1, G n s) from funext hcoeff]
  convert hsum using 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  exact (heq s hs).symm

end
end IsingBulk.Preferred22.DividedDifferenceFoundation
