import IsingBulk.Tail.OriginalLowerDensity
import Mathlib.MeasureTheory.Integral.Pi

/-! Actual normalized K integral on the original c epsilon disk. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set MeasureTheory
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem original_lower_integral_gaussian_bound (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η < η₀ →
      ∃ α₀ c e C K κ : ℝ, 0 < α₀ ∧ 0 < c ∧ 0 < e ∧ 0 < C ∧ 0 < K ∧ 0 < κ ∧
      ∀ α : ℝ, 0 < α → α < α₀ → ∀ (N : ℕ) (eps τ : ℝ) (s : ℂ),
        2 ≤ N → 0 < eps → eps < e → ‖s-radialParameter d.theta eps‖ ≤ c*eps →
        ‖originalLowerIntegral N (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ s‖ ≤
          K*C^N*eps⁻¹^2*Real.exp (-κ*(N:ℝ)^2) := by
  obtain ⟨η₀,hη₀,hpair⟩ := original_actual_source_pair_product d hcsmall
  obtain ⟨W,cW,eW,hW,hcW,heW,hbody⟩ := original_residue_l1_oneperiod d hcsmall
  have hsint : 0 < Real.sin d.theta := Real.sin_pos_of_pos_of_lt_pi d.theta_pos
    (by linarith [d.theta_lt,Real.pi_pos])
  obtain ⟨cG,eG,A,G,hcG,heG,hA,hG,hglobal⟩ := original_disk_global_factors d.theta d.c₀ hsint d.c₀_pos hcsmall
  refine ⟨η₀,hη₀,?_⟩
  intro η hη hηlt
  obtain ⟨α₀,cP,eP,P,κ,hα₀,hcP,heP,hP,hκ,hpairs⟩ := hpair η hη hηlt
  let c := min cP (min cW cG)
  let H := max A (Real.exp d.c₀)
  let D := (2*Real.pi)⁻¹*H*P
  have hH : 0 < H := lt_of_lt_of_le hA (le_max_left _ _)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨α₀,c,min eP (min eW (min eG 1)),D*W,2*G,κ,hα₀,
    lt_min hcP (lt_min hcW hcG),lt_min heP (lt_min heW (lt_min heG zero_lt_one)),
    mul_pos hD hW,by positivity,hκ,?_⟩
  intro α hα hαlt N eps τ s hN heps hepslt hs
  have heP' := hepslt.trans_le (min_le_left _ _)
  have heW' := hepslt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have heG' := hepslt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have he1 : eps ≤ 1 := hepslt.le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hsP := hs.trans (mul_le_mul_of_nonneg_right (min_le_left cP _) heps.le)
  have hsW := hs.trans (mul_le_mul_of_nonneg_right ((min_le_right cP _).trans (min_le_left cW cG)) heps.le)
  have hsG := hs.trans (mul_le_mul_of_nonneg_right ((min_le_right cP _).trans (min_le_right cW cG)) heps.le)
  obtain ⟨hmargin,hzi,hgap⟩ := hglobal eps heps heG' s hsG
  obtain ⟨hwcont,hwint⟩ := hbody eps heps heW' s hsW
  let r := Real.exp (-d.c₀*eps)
  let f := constructedSelector d.thetaB η α
  let w := fun t => ‖residueFactor (globalRoot s (anglePoint r t))‖
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [d.c₀_pos])
  have hm : r⁻¹-r < (sourceS s).im := by simpa only [r,neg_mul,Real.exp_neg,inv_inv] using hmargin
  have ha := globalRoot_admissible hr hr1 hm
  have hri : r⁻¹ ≤ Real.exp d.c₀ := by
    dsimp [r]
    rw [neg_mul,Real.exp_neg,inv_inv]
    apply Real.exp_le_exp.mpr
    nlinarith [d.c₀_pos]
  have hmax : max A r⁻¹ ≤ H := max_le_max le_rfl hri
  have hden : (1-r^2)⁻¹^2 ≤ G*eps⁻¹^2 := by
    have he : r^2=Real.exp (-2*d.c₀*eps) := by dsimp [r]; rw [← Real.exp_nat_mul]; congr 1; ring
    simpa only [he] using hgap
  have hw0 (t : ℝ) : 0 ≤ w t := norm_nonneg _
  have hip : IntegrableOn (fun θ : Fin N → ℝ => ∏ i,w (θ i)) (angleBox N) := by
    rw [IntegrableOn,angleBox_restrict_pi]
    exact Integrable.fintype_prod (fun _ : Fin N => hwcont.continuousOn.integrableOn_compact isCompact_Icc)
  have hpint : (∫ θ in angleBox N,∏ i,w (θ i)) ≤ W^N := by
    rw [angleBox_restrict_pi,integral_fintype_prod_eq_pow,Fintype.card_fin]
    exact pow_le_pow_left₀ (integral_nonneg hw0) hwint N
  let T := 2*G*D^N*eps⁻¹^2*Real.exp (-κ*(N:ℝ)^2)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hpoint (θ : Fin N → ℝ) (hθ : θ ∈ angleBox N) :
      ‖(angularSelector f θ:ℂ)*pulledDensity f r τ 0 s θ‖ ≤ T*(∏ i,w (θ i)) := by
    by_cases hsupport : θ ∈ tsupport (angularSelector f)
    · have hy (i : Fin N) : ‖angleTuple r θ i‖=r := anglePoint_norm hr.le _
      have hz := (ha.toTuple N (angleTuple r θ) hy).root_inside
      have hpa := hpairs α hα hαlt N eps θ s heps heP' hθ hsupport hsP
      have hd := original_canceled_density_complete_bound hN hr hr1 hA.le hP.le
        (fun i => globalRoot s (anglePoint r (θ i))) (angleTuple r θ)
        (fun i => (hz i).le) hy (fun i => hzi _ (hy i)) hpa
      have hdb : ‖canceledReducedDensity (fun i => globalRoot s (anglePoint r (θ i))) (angleTuple r θ)‖ ≤
          (2*G*(H*P)^N*eps⁻¹^2)*Real.exp (-κ*(N:ℝ)^2)*(∏ i,w (θ i)) := by
        apply hd.trans
        have hmP : max A r⁻¹*P ≤ H*P := mul_le_mul_of_nonneg_right hmax hP.le
        have he : 2*(max A r⁻¹*P)^N/(1-r^2)^2=2*(max A r⁻¹*P)^N*((1-r^2)⁻¹^2) := by rw [div_eq_mul_inv,inv_pow]
        rw [he]
        have hscale := mul_le_mul (pow_le_pow_left₀ (by positivity) hmP N) hden
          (by positivity : 0 ≤ (1-r^2)⁻¹^2) (by positivity : 0 ≤ (H*P)^N)
        have hcoef : 2*(max A r⁻¹*P)^N*((1-r^2)⁻¹^2) ≤ 2*G*(H*P)^N*eps⁻¹^2 := by
          nlinarith only [hscale]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le)
          (Finset.prod_nonneg (fun i _ => norm_nonneg _))
      have hf : (N.factorial:ℝ)⁻¹ ≤ 1 := by
        apply inv_le_one_of_one_le₀
        exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos N)
      have hrad : (r/(2*Real.pi))^N ≤ ((2*Real.pi)⁻¹)^N :=
        pow_le_pow_left₀ (by positivity) (by simpa only [one_div] using div_le_div_of_nonneg_right hr1.le (by positivity : 0≤2*Real.pi)) N
      rw [norm_mul,original_pulledDensity_norm f hr.le]
      calc
        _ ≤ 1*(1*((2*Real.pi)⁻¹)^N*((2*G*(H*P)^N*eps⁻¹^2)*Real.exp (-κ*(N:ℝ)^2)*(∏ i,w (θ i)))) := by
          gcongr
          exact constructed_original_weight_norm_le d.thetaB η α θ
        _ = _ := by dsimp [T,D]; simp only [mul_pow]; ring
    · have hz := image_eq_zero_of_notMem_tsupport (f := angularSelector f) hsupport
      rw [hz,Complex.ofReal_zero,zero_mul,norm_zero]
      exact mul_nonneg hT (Finset.prod_nonneg (fun i _ => hw0 (θ i)))
  have hnorm : ‖originalLowerIntegral N f r τ s‖ ≤ T*W^N := by
    apply (norm_integral_le_of_norm_le (hip.const_mul T) ?_).trans
      ((integral_const_mul T _).trans_le (mul_le_mul_of_nonneg_left hpint hT))
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    exact hpoint θ hθ
  convert hnorm using 1
  dsimp [T]
  rw [mul_pow]
  ring

end
end IsingBulk.Tail
