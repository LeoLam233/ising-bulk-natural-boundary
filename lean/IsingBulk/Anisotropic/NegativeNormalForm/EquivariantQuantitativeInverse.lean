import IsingBulk.Anisotropic.NegativeNormalForm.QuantitativeProjectedInverse
import IsingBulk.Anisotropic.NegativeNormalForm.QuantitativeInverseAnalytic

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Set Metric Filter
open scoped Topology

theorem exists_equivariant_quantitative_inverse {n : ℕ}
    (F : Config n → Config n) (r : ℝ) (hr : 0<r) (c : NNReal) (hc : (c:ℝ)<1)
    (hF : AnalyticOnNhd ℂ F (ball 0 r)) (hF0 : F 0=0)
    (hdF : HasFDerivAt F (ContinuousLinearMap.id ℂ (Config n)) 0)
    (heq : ∀ e : Equiv.Perm (Fin n), ∀ v, F (permute e v)=permute e (F v))
    (hLip : LipschitzOnWith c (fun v => F v-v) (closedBall 0 r)) :
    ∃ V : Config n → Config n,
      AnalyticOnNhd ℂ V (ball 0 ((1-(c:ℝ))*r)) ∧ V 0=0 ∧
      HasFDerivAt V (ContinuousLinearMap.id ℂ (Config n)) 0 ∧
      (∀ e : Equiv.Perm (Fin n), ∀ v, V (permute e v)=permute e (V v)) ∧
      (∀ y, ‖y‖≤(1-(c:ℝ))*r →
        V y∈closedBall 0 r ∧ F (V y)=y ∧ ‖V y‖≤‖y‖/(1-(c:ℝ))) ∧
      (∀ y z, ‖y‖≤(1-(c:ℝ))*r → ‖z‖≤(1-(c:ℝ))*r →
        ‖V y-V z‖≤‖y-z‖/(1-(c:ℝ))) := by
  obtain ⟨V,hV0,hV,hVLip⟩ := exists_quantitative_inverse F r hr.le c hc hF0 hLip
  have hVeq (e : Equiv.Perm (Fin n)) (y : Config n) (hy : ‖y‖≤(1-(c:ℝ))*r) :
      V (permute e y)=permute e (V y) := by
    have hey : ‖permute e y‖≤(1-(c:ℝ))*r := by simpa using hy
    apply perturbation_injOn F _ c hc hLip (hV _ hey).1
    · simpa only [mem_closedBall,dist_zero_right,norm_permute] using (hV y hy).1
    · rw [(hV _ hey).2.1,heq]
      exact congrArg (permute e) (hV y hy).2.1.symm
  have havg (y : Config n) (hy : ‖y‖≤(1-(c:ℝ))*r) : equivariantAverage V y=V y :=
    equivariantAverage_eq_at V y (fun e => hVeq e y hy)
  have hR : 0<(1-(c:ℝ))*r := mul_pos (sub_pos.mpr hc) hr
  have hVA (y : Config n) (hy : ‖y‖≤(1-(c:ℝ))*r) :
      equivariantAverage V y∈closedBall 0 r ∧ F (equivariantAverage V y)=y ∧
      ‖equivariantAverage V y‖≤‖y‖/(1-(c:ℝ)) := by
    rw [havg y hy]
    exact hV y hy
  have ha := quantitative_inverse_analyticOnNhd F (equivariantAverage V) r hr c hc hLip hF hVA
  have hazero : equivariantAverage V 0=0 := by
    rw [havg 0 (by simpa using hR.le),hV0]
  have ha0 : AnalyticAt ℂ (equivariantAverage V) 0 := ha 0 (by simpa using hR)
  have hdF' : HasFDerivAt F (ContinuousLinearMap.id ℂ (Config n)) (equivariantAverage V 0) := by
    rw [hazero]; exact hdF
  have hcomp : (fun y => F (equivariantAverage V y)) =ᶠ[𝓝 0] id := by
    filter_upwards [closedBall_mem_nhds (0:Config n) hR] with y hy
    exact (hVA y (by simpa using hy)).2.1
  have hdcomp : HasFDerivAt (fun y => F (equivariantAverage V y))
      (ContinuousLinearMap.id ℂ (Config n)) 0 :=
    (hasFDerivAt_id (0:Config n)).congr_of_eventuallyEq hcomp
  have hchain := hdF'.comp 0 ha0.differentiableAt.hasFDerivAt
  have hder := hchain.unique hdcomp
  simp only [ContinuousLinearMap.id_comp] at hder
  have hdV := ha0.differentiableAt.hasFDerivAt
  rw [hder] at hdV
  refine ⟨equivariantAverage V,ha,hazero,hdV,equivariantAverage_permute V,hVA,?_⟩
  intro y z hy hz
  rw [havg y hy,havg z hz]
  exact hVLip y z hy hz

end
end IsingBulk.Anisotropic.NegativeNormalForm
