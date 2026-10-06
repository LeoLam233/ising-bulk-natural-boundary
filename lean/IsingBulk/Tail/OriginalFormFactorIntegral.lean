import IsingBulk.Tail.OriginalDensityMajorant

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch MeasureTheory Set
open scoped BigOperators Topology
set_option maxHeartbeats 1000000

theorem original_formFactor_weighted_integral (d : LocalBranchData) (n : ℕ) (hn : 0 < n)
    {e : ℝ} (he : 0 < e) {s : ℂ}
    (hm : (Real.exp (-d.c₀*e))⁻¹-Real.exp (-d.c₀*e) < (sourceS s).im)
    {A : ℝ} (hA : 0 ≤ A)
    (hi : ∀ y : ℂ, ‖y‖=Real.exp (-d.c₀*e) → ‖(globalRoot s y)⁻¹‖ ≤ A) :
    ‖doubleFormFactor (2*n) (Real.exp (-d.c₀*e)) s‖ ≤
      ((2*n).factorial:ℝ)⁻¹ * (Real.exp (-d.c₀*e)/(2*Real.pi))^(2*n) *
      (2*(max A (Real.exp (-d.c₀*e))⁻¹)^(2*n)/(1-(Real.exp (-d.c₀*e))^2)^2)*
      originalWeightedPfaffianIntegral d n e s := by
  let r := Real.exp (-d.c₀*e)
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [d.c₀_pos])
  have ha := globalRoot_admissible hr hr1 hm
  let W : (Fin (2*n) → ℝ) → ℝ := fun x =>
    ((List.finRange (2*n)).map (fun a => ‖originalResidueAngle d e s (x a)‖)).prod *
    ‖labelPfaffian (fun a b => pairKernel (anglePoint r (x a)) (anglePoint r (x b))) n
      (List.finRange (2*n))‖
  let K := (r/(2*Real.pi))^(2*n) * (2*(max A r⁻¹)^(2*n)/(1-r^2)^2)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hR : Continuous (originalResidueAngle d e s) := by
    apply originalResidueAngle_continuous
    intro theta
    rw [radialAnglePoint_eq_anglePoint_exp]
    exact sourceW_upper_of_margin hr hr1 hm (anglePoint_norm hr.le theta)
  have hW : Continuous W := by
    have hpf : Continuous (fun x : Fin (2*n) → ℝ =>
        labelPfaffian (fun a b => pairKernel (anglePoint r (x a)) (anglePoint r (x b))) n
          (List.finRange (2*n))) :=
      continuous_labelPfaffian _ (fun a b =>
        (original_y_pair_continuous hr.le hr1).comp
          (show Continuous (fun x : Fin (2*n) → ℝ => (x a,x b)) from
            (continuous_apply a).prodMk (continuous_apply b))) n _
    exact (continuous_list_prod_map (fun (x : Fin (2*n) → ℝ) a => ‖originalResidueAngle d e s (x a)‖)
      (fun a => hR.norm.comp (continuous_apply a)) _).mul hpf.norm
  have hsource := sourceReducedAngularDensity_continuous (2*n) (by omega) hr hr1 hm
  have hp (x : Fin (2*n) → ℝ) : ‖sourceReducedAngularDensity r s x‖ ≤ K*W x := by
    have hy (i : Fin (2*n)) : ‖anglePoint r (x i)‖=r := anglePoint_norm hr.le _
    have hz := (ha.toTuple (2*n) (angleTuple r x) hy).root_inside
    have hb := reducedDensity_weighted_bound (by omega : 2 ≤ 2*n) hr hr1 hA
      (fun i => globalRoot s (anglePoint r (x i))) (angleTuple r x) (fun i => (hz i).le)
      hy (fun i => hi _ (hy i)) (original_root_pairProduct_norm hr hr1 hm _ hy)
    rw [sourceReducedAngularDensity,norm_mul,norm_angleProductJacobian hr.le]
    apply (mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq
    rw [circle_pairProduct_eq_labelPfaffian n hr1 (angleTuple r x) (fun i => (hy i).le)]
    simp only [W,K,angleTuple,originalResidueAngle,radialAnglePoint_eq_anglePoint_exp,← List.ofFn_eq_map,
      List.prod_ofFn]
    dsimp only [r]
    ring
  have hib : IntegrableOn (sourceReducedAngularDensity (N := 2*n) r s) (angleBox (2*n)) :=
    hsource.continuousOn.integrableOn_compact isCompact_Icc
  have hiW : IntegrableOn W (angleBox (2*n)) :=
    hW.continuousOn.integrableOn_compact isCompact_Icc
  have hI : ‖∫ x in angleBox (2*n), sourceReducedAngularDensity r s x‖ ≤
      K*originalWeightedPfaffianIntegral d n e s := by
    apply (norm_integral_le_integral_norm _).trans
    apply (setIntegral_mono_on hib.norm (hiW.const_mul K) measurableSet_Icc
      (fun x _ => hp x)).trans_eq
    rw [integral_const_mul]
    congr 1
    rw [angleBox_restrict_pi]
    rfl
  rw [source_angular_integral_identity (2*n) (by omega) hr hr1 hm,norm_mul,norm_inv,
    Complex.norm_natCast]
  have hh := mul_le_mul_of_nonneg_left hI (by positivity : 0 ≤ ((2*n).factorial:ℝ)⁻¹)
  convert hh using 1
  dsimp [K,r]
  ring

end
end IsingBulk.Tail
