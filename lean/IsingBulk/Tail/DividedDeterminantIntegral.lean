import IsingBulk.Tail.CompactFreezingDeterminant
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace IsingBulk.Tail
noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

def pairInsertionCLM {N : ℕ} (i j : Fin N) :
    ((ℝ × ℝ) × (Fin N → ℝ)) →L[ℝ] (Fin N → ℝ) :=
  ContinuousLinearMap.pi (fun l => if l=i then
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ×ℝ) (Fin N→ℝ)) else
    if l=j then (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ×ℝ) (Fin N→ℝ)) else
    (ContinuousLinearMap.proj l).comp (ContinuousLinearMap.snd ℝ (ℝ×ℝ) (Fin N→ℝ)))

lemma pairInsertionCLM_apply {N : ℕ} (i j : Fin N) (z : (ℝ × ℝ) × (Fin N→ℝ)) :
    pairInsertionCLM i j z=pairInsertion i j z := by
  funext l
  by_cases hi : l=i
  · simp [pairInsertionCLM,pairInsertion,hi]
  · by_cases hj : l=j
    · have hji : j≠i := by simpa only [hj] using hi
      simp [pairInsertionCLM,pairInsertion,hj,hji]
    · simp [pairInsertionCLM,pairInsertion,hi,hj]

lemma pairInsertionCLM_first {N : ℕ} (i j : Fin N) :
    pairInsertionCLM i j (((1,0),0) : (ℝ × ℝ) × (Fin N→ℝ))=Pi.single i 1 := by
  funext l
  by_cases hi : l=i
  · simp [pairInsertionCLM,hi]
  · by_cases hj : l=j
    · have hji : j≠i := by simpa only [hj] using hi
      simp [pairInsertionCLM,hj,hji]
    · simp [pairInsertionCLM,hi,hj]

lemma pairInsertion_transverse {N : ℕ} (i j : Fin N) (x : Fin N→ℝ) (t : ℝ) :
    pairInsertion i j (diagonalLine ((x i,x j),x) t)=Function.update x i (x j+t*(x i-x j)) := by
  funext l
  by_cases hi : l=i
  · subst l; simp [pairInsertion,diagonalLine]
  · by_cases hj : l=j
    · subst l; simp [pairInsertion,diagonalLine,hi]
    · simp [pairInsertion,diagonalLine,hi,hj]

lemma angularPairDividedDifference_integral {N : ℕ} (F G : (Fin N→ℝ)→ℂ)
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (i j : Fin N) (x : Fin N→ℝ) :
    angularPairDividedDifference F G i j x = ∫ t in (0:ℝ)..1,
      fderiv ℝ (angularPairDeterminant F G i j)
        (Function.update x i (x j+t*(x i-x j))) (Pi.single i 1) := by
  unfold angularPairDividedDifference smoothDividedDifference
  apply intervalIntegral.integral_congr
  intro t ht
  let z := diagonalLine ((x i,x j),x) t
  have hd := ((angularPairDeterminant_smooth hF hG i j).differentiable (by simp)
    (pairInsertionCLM i j z)).hasFDerivAt.comp z (pairInsertionCLM i j).hasFDerivAt
  have he := congrArg (fun L => L (((1,0),0) : (ℝ×ℝ)×(Fin N→ℝ))) hd.fderiv
  simp only [ContinuousLinearMap.comp_apply,pairInsertionCLM_first] at he
  simpa only [Function.comp_def,pairInsertionCLM_apply,z,pairInsertion_transverse] using he

lemma angularPairDividedDifference_im_margin {N : ℕ} (F G : (Fin N→ℝ)→ℂ)
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (i j : Fin N) (x : Fin N→ℝ)
    (c : ℝ) (hb : ∀ t ∈ Icc (0:ℝ) 1,
      c ≤ (fderiv ℝ (angularPairDeterminant F G i j)
        (Function.update x i (x j+t*(x i-x j))) (Pi.single i 1)).im) :
    c ≤ ‖angularPairDividedDifference F G i j x‖ := by
  let H : ℝ→ℂ := fun t => fderiv ℝ (angularPairDeterminant F G i j)
    (Function.update x i (x j+t*(x i-x j))) (Pi.single i 1)
  have hpath : Continuous (fun t : ℝ => Function.update x i (x j+t*(x i-x j))) := by fun_prop
  have hc : Continuous H := ((angularPairDeterminant_smooth hF hG i j).continuous_fderiv
    (by simp)).comp hpath |>.clm_apply continuous_const
  have hi : IntervalIntegrable H volume 0 1 := hc.intervalIntegrable 0 1
  have he : (∫ t in (0:ℝ)..1, H t).im = ∫ t in (0:ℝ)..1, (H t).im := by
    exact (Complex.imCLM.intervalIntegral_comp_comm hi).symm
  have hlow : c ≤ ∫ t in (0:ℝ)..1, (H t).im := by
    have hh := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0:ℝ)≤1)
      intervalIntegrable_const ((Complex.continuous_im.comp hc).intervalIntegrable 0 1)
      (fun t ht => hb t ht)
    simpa using hh
  rw [angularPairDividedDifference_integral F G hF hG]
  exact (hlow.trans_eq he.symm).trans (Complex.im_le_norm _)

end
end IsingBulk.Tail
