import IsingBulk.Tail.OriginalBranchMajorant
import IsingBulk.Tail.OriginalGlobalDisk
import IsingBulk.Tail.ConstructedCurrentDisk
import IsingBulk.Tail.SelectedFActualOneBody

/-! Uniform integrable one-body majorant on the actual named-current support.
The occupancy remains the coupled sum of actual cutoff values. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter Metric
open scoped Topology BigOperators

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1500000 in
 theorem original_current_actual_onebody_bound (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ η₀ τ₀ : ℝ, 0 < η₀ ∧ 0 < τ₀ ∧
      ∀ η α τ : ℝ, 0 < η → η < η₀ → 0 < α → α < Real.sin d.thetaB/4 →
        0 < τ → τ < τ₀ → ∃ C c eps₀ : ℝ, 0 < C ∧ 0 < c ∧ 0 < eps₀ ∧
        ∀ (N : ℕ) (eps lam : ℝ) (θ : Fin N → ℝ) (q : Fin N) (s : ℂ),
          1 ≤ N → 0 < eps → eps < eps₀ → 0 ≤ lam → lam ≤ 1 → θ ∈ angleBox N →
          θ ∈ tsupport (namedSelectorDerivative (constructedSelector d.thetaB η α) q) →
          ‖s-radialParameter d.theta eps‖ ≤ c*eps → ∀ i,
          ‖residueFactor (selectedContinuedRoot s
            (deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ lam θ i))‖ ≤
            selectedOneBodyBound d.thetaB η C eps (θ i) := by
  obtain ⟨CB,cB,r,hCB,hcB,hr,hbranch⟩ := original_disk_branch_onebody d
  have hsint : 0 < Real.sin d.theta := Real.sin_pos_of_pos_of_lt_pi d.theta_pos
    (by linarith [d.theta_lt,Real.pi_pos])
  obtain ⟨cG,eG,hcG,_hcG1,heG,_heG1,hupper⟩ := original_disk_sourceW_upper d.theta d.c₀ hsint d.c₀_pos hcsmall
  obtain ⟨ηA,hηA,hcoord⟩ := lowerChord_small_coordinate d.thetaB_pos d.thetaB_lt hr
  have hsinb : 0 < Real.sin d.thetaB := d.a_pos
  have hS : 0 < 1+Real.cos d.thetaB := by
    have hh' := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos,d.theta_pos],d.theta_lt⟩
    linarith [d.angle_relation]
  let η₀ := min ηA (Real.sin d.thetaB/4)
  let τ₀ := min r (min (1/2:ℝ) ((1+Real.cos d.thetaB)/8))
  refine ⟨η₀,τ₀,lt_min hηA (by positivity),lt_min hr (lt_min (by norm_num) (by positivity)),?_⟩
  intro η α τ hη hηlt hα hαsmall hτ hτlt
  have hηsmall : η ≤ Real.sin d.thetaB/4 := hηlt.le.trans (min_le_right _ _)
  have hηA' : η ≤ ηA := hηlt.le.trans (min_le_left _ _)
  have hτr : τ < r := hτlt.trans_le (min_le_left _ _)
  have hτsmall : 2*τ ≤ 1 := by
    have hh' := hτlt.le.trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hτS : 4*τ < 1+Real.cos d.thetaB := by
    have hh' := hτlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  obtain ⟨epsK,hepsK,_hepsK1,K,hK,hKD,hcover⟩ := current_regular_center_compact
    (c₀ := d.c₀) d.angle_relation hsinb hη hηsmall hα hαsmall hτ hτsmall hτS
  obtain ⟨cK,CK,hcK,hCK,hcompact⟩ := continuedRoot_compact_onebody hK hKD
  let c := min (min cB cG) (min (1/4:ℝ) (cK/3))
  let eps₀ := min epsK (min r (min 1 eG))
  let C := max CB CK
  have hc : 0 < c := lt_min (lt_min hcB hcG) (lt_min (by norm_num) (by positivity))
  have hcB' : c ≤ cB := (min_le_left _ _).trans (min_le_left _ _)
  have hcG' : c ≤ cG := (min_le_left _ _).trans (min_le_right _ _)
  have hc1 : c ≤ 1/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hcK' : c ≤ cK/3 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨C,c,eps₀,lt_of_lt_of_le hCB (le_max_left _ _),hc,lt_min hepsK (lt_min hr (lt_min zero_lt_one heG)),?_⟩
  intro N eps lam θ q s hN heps hepslt hl0 hl1 hθ hsupport hsd i
  let f := constructedSelector d.thetaB η α
  let P := occupancy (fun i => f.p (θ i))
  let ρ := P/(N:ℝ)
  let y := deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0:ℝ) < N := by linarith
  have hepsK' : eps ≤ epsK := hepslt.le.trans (min_le_left _ _)
  have hepsr : eps < r := hepslt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hp0 : ∀ x, 0 ≤ f.p x := fun x => (thresholdStep_range _ _ _).1
  have hp1 : ∀ x, f.p x ≤ 1 := fun x => (thresholdStep_range _ _ _).2
  obtain ⟨hqp,_hqm,_hqsin,hallSin,_hqch⟩ :=
    constructed_current_support_geometry d.thetaB η α hsinb hη hηsmall hα q hsupport
  have heps1 : eps ≤ 1 := hepslt.le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hepsG : eps < eG := hepslt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hradius : c*eps ≤ c := mul_le_of_le_one_right hc.le heps1
  have hphys (k : Fin N) : 0<(sourceW s (y k)).im := by
    have hb := hupper eps heps hepsG s (hsd.trans (mul_le_mul_of_nonneg_right hcG' heps.le)) (θ k)
    have hbase : 0<(sourceW s (deformedPoint f (Real.exp (-d.c₀*eps)) τ 0 θ k)).im := by
      simpa only [deformedPoint_coupledRadialExponent,coupledRadialExponent,zero_mul,zero_add,add_zero] using hb
    exact hbase.trans_le (deformed_sourceW_im_ge (by omega) f (Real.exp_pos _) hτ.le hl0 θ s
      (fun x => (thresholdStep_range _ _ _).1) (fun x => Real.smoothTransition.nonneg _)
      (fun x hx => thresholdStep_zero (by linarith) (by linarith))
      (fun x hx => lowerM_zero_of_nonneg_sine d.thetaB η x d.a_pos hη hηsmall hx) k)
  have hP : 1 ≤ P := occupancy_named (fun i => hp0 (θ i)) q hqp
  have hPN : P ≤ N := occupancy_le (fun i => hp1 (θ i))
  have hρ0 : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hρ1 : ρ ≤ 1 := (div_le_one hn0).mpr hPN
  by_cases hcore : lowerChord d.thetaB (θ i) < η^2/2
  · simp only [selectedOneBodyBound,hcore,ite_true]
    have hch : lowerChord d.thetaB (θ i) ≤ η^2 := by linarith [sq_nonneg η]
    obtain ⟨hmi,hpi⟩ := constructed_lower_core_plateau hsinb hη hηsmall hα hch
    let u := θ i+d.thetaB-2*Real.pi
    have hu : |u| < r := hcoord (θ i) (hθ.1 i) (hθ.2 i)
      (hch.trans (pow_le_pow_left₀ hη.le hηA' 2))
    have hyp : y i=plateauY d.c₀ eps τ (lam*P/(N:ℝ)) d.thetaB u :=
      deformedPoint_current_plateau f d.thetaB d.c₀ eps τ lam θ i hpi hmi
    have hsB := hsd.trans (mul_le_mul_of_nonneg_right hcB' heps.le)
    have ht0 : 0 ≤ lam*P/(N:ℝ) := by positivity
    have ht1 : lam*P/(N:ℝ) ≤ 1 := (div_le_one hn0).mpr ((mul_le_of_le_one_left (by positivity : 0≤P) hl1).trans hPN)
    have hbnd := hbranch τ eps (lam*P/(N:ℝ)) u s hτ.le hτr heps hepsr ht0 ht1 hu hsB
    change ‖residueFactor (selectedContinuedRoot s (y i))‖ ≤ _
    rw [show selectedContinuedRoot s (y i)=interiorRoot (sourceW s (y i)) from continuedRoot_eq_interiorRoot (hphys i),hyp]
    have hdisp : IsingBulk.Branch.dispersion s (plateauY d.c₀ eps τ (lam*P/(N:ℝ)) d.thetaB u)=sourceW s (plateauY d.c₀ eps τ (lam*P/(N:ℝ)) d.thetaB u) := by unfold IsingBulk.Branch.dispersion sourceW sourceS; ring
    rw [hdisp] at hbnd
    exact hbnd.trans (div_le_div_of_nonneg_right (le_max_left CB CK) (Real.sqrt_nonneg _))
  · simp only [selectedOneBodyBound,hcore,ite_false]
    let W₀ := sourceW (radialParameter d.theta eps) (y i)
    let W := sourceW s (y i)
    have hW₀ : W₀ ∈ K := by
      change sourceW _ (y i) ∈ K
      dsimp only [y]
      rw [deformedPoint_scale_lambda,deformedPoint_selected_formula]
      exact hcover eps heps.le hepsK' (lam,(ρ,θ i))
        ⟨⟨hl0,hl1⟩,⟨⟨⟨hρ0,hρ1⟩,⟨⟨hθ.1 i,hθ.2 i⟩,le_of_not_gt hcore⟩⟩,hallSin i⟩⟩
    have hsmall : ‖s-radialParameter d.theta eps‖ < (1:ℝ)/2 := by
      have hh' : c*eps ≤ c := hradius
      linarith only [hsd,hh',hc1]
    have hnorm : 1 ≤ ‖radialParameter d.theta eps‖ := by rw [radialParameter_norm heps.le]; linarith
    have hsn := norm_ge_half_of_near_unit hnorm hsmall
    have hdiff : ‖W-W₀‖ ≤ cK := by
      have he : W-W₀=sourceS s-sourceS (radialParameter d.theta eps) := by dsimp [W,W₀,sourceW]; ring
      rw [he]
      have htrace := sourceS_sub_norm_le hsn hnorm
      have hcN : c*eps ≤ c := hradius
      linarith only [htrace,hsd,hcN,hcK']
    exact ((hcompact W₀ hW₀ W hdiff).1).trans (le_max_right CB CK)

end
end IsingBulk.Tail
