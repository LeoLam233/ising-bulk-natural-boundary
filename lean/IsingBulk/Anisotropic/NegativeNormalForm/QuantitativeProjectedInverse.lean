import IsingBulk.Anisotropic.NegativeNormalForm.InverseGermAgreement
import IsingBulk.Anisotropic.NegativeNormalForm.ProjectedUniformEstimates
import IsingBulk.Anisotropic.NegativeNormalForm.EquivariantInverse

/-! Common-domain inverse representatives for the actual projected extension.
The displayed Lipschitz premise is an explicit remaining scalar-estimate input,
not a claim that such a bound has already been proved for the physical phase. -/
noncomputable section
open Set Metric Filter
open scoped Topology
namespace IsingBulk.Anisotropic.NegativeNormalForm

 theorem equivariantAverage_eq_at {n : ℕ} (V : Config n → Config n) (y : Config n)
    (h : ∀ e : Equiv.Perm (Fin n), V (permute e y)=permute e (V y)) :
    equivariantAverage V y=V y := by
  ext i
  have hc : (Fintype.card (Equiv.Perm (Fin n)):ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp_rw [equivariantAverage,h]
  simp [permute,hc]

 theorem exists_quantitative_equivariant_projected_inverse {n : ℕ} (hn : n ≠ 0)
    (U : Config n → Config n) (hU : AnalyticAt ℂ U 0) (hU0 : U 0=0)
    (hdU : HasFDerivAt U (ContinuousLinearMap.id ℂ (Config n)) 0)
    (hUeq : ∀ e : Equiv.Perm (Fin n), ∀ v, U (permute e v)=permute e (U v))
    (r : ℝ) (hr : 0<r) (c : NNReal) (hc : (c:ℝ)<1)
    (hLip : LipschitzOnWith c (fun v => projectedExtension U v-v) (closedBall 0 r)) :
    ∃ V : Config n → Config n,
      AnalyticAt ℂ V 0 ∧ V 0=0 ∧
      HasFDerivAt V (ContinuousLinearMap.id ℂ (Config n)) 0 ∧
      (∀ e : Equiv.Perm (Fin n), ∀ v, V (permute e v)=permute e (V v)) ∧
      (∀ y, ‖y‖≤(1-(c:ℝ))*r →
        V y ∈ closedBall 0 r ∧ projectedExtension U (V y)=y ∧ ‖V y‖≤‖y‖/(1-(c:ℝ)) ∧
        (ZeroMean y → ZeroMean (V y) ∧ project (U (V y))=y)) ∧
      (∀ y z, ‖y‖≤(1-(c:ℝ))*r → ‖z‖≤(1-(c:ℝ))*r →
        ‖V y-V z‖≤‖y-z‖/(1-(c:ℝ))) := by
  let F := projectedExtension U
  obtain ⟨V,hV0,hV,hVLip⟩ := exists_quantitative_inverse F r hr.le c hc
    (projectedExtension_zero U hU0) hLip
  obtain ⟨W,hW,hW0,hdW,_hleft,hWinv⟩ := exists_projected_inverse hn U hU hU0 hdU
  have heW : V =ᶠ[𝓝 0] W := quantitative_inverse_eq_germ F V W r hr c hc hLip
    (fun y hy => ⟨(hV y hy).1,(hV y hy).2.1⟩) hW.continuousAt hW0 (hWinv.mono fun _ h => h.1)
  have hVeq (e : Equiv.Perm (Fin n)) (y : Config n) (hy : ‖y‖≤(1-(c:ℝ))*r) :
      V (permute e y)=permute e (V y) := by
    have hey : ‖permute e y‖≤(1-(c:ℝ))*r := by simpa using hy
    apply perturbation_injOn F _ c hc hLip (hV _ hey).1
    · simpa only [mem_closedBall,dist_zero_right,norm_permute] using (hV y hy).1
    · rw [(hV _ hey).2.1]
      change permute e y=projectedExtension U (permute e (V y))
      rw [projectedExtension_permute U hUeq]
      exact congrArg (permute e) (hV y hy).2.1.symm
  have havg (y : Config n) (hy : ‖y‖≤(1-(c:ℝ))*r) : equivariantAverage V y=V y :=
    equivariantAverage_eq_at V y (fun e => hVeq e y hy)
  have hR : 0<(1-(c:ℝ))*r := mul_pos (sub_pos.mpr hc) hr
  have hea : equivariantAverage V =ᶠ[𝓝 0] V := by
    filter_upwards [closedBall_mem_nhds (0:Config n) hR] with y hy
    exact havg y (by simpa using hy)
  have ha : AnalyticAt ℂ (equivariantAverage V) 0 := hW.congr (hea.trans heW).symm
  have hd : HasFDerivAt (equivariantAverage V) (ContinuousLinearMap.id ℂ (Config n)) 0 :=
    hdW.congr_of_eventuallyEq (hea.trans heW)
  have hazero : equivariantAverage V 0=0 := by
    rw [havg 0 (by simpa using hR.le),hV0]
  refine ⟨equivariantAverage V,ha,hazero,hd,equivariantAverage_permute V,?_,?_⟩
  · intro y hy
    rw [havg y hy]
    refine ⟨(hV y hy).1,(hV y hy).2.1,(hV y hy).2.2,?_⟩
    intro hmy
    have hmV : ZeroMean (V y) := (projectedExtension_zeroMean_iff hn U (V y)).mp
      (by change ZeroMean (F (V y)); rw [(hV y hy).2.1]; exact hmy)
    exact ⟨hmV,(projectedExtension_on_zeroMean U hmV).symm.trans (hV y hy).2.1⟩
  · intro y z hy hz
    rw [havg y hy,havg z hz]
    exact hVLip y z hy hz

end IsingBulk.Anisotropic.NegativeNormalForm
