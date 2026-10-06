import IsingBulk.Tail.ProtectedBranchOneBody
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
 theorem protected_actual_onebody_bound (d : LocalBranchData) :
    ∃ η₀ τ₀ : ℝ, 0 < η₀ ∧ 0 < τ₀ ∧
      ∀ η α τ : ℝ, 0 < η → η < η₀ → 0 < α → α < Real.sin d.thetaB/4 →
        0 < τ → τ < τ₀ → ∃ C c eps₀ : ℝ, 0 < C ∧ 0 < c ∧ 0 < eps₀ ∧
        ∀ (N : ℕ) (eps lamStar lam : ℝ) (θ : Fin N → ℝ) (q : Fin N) (s : ℂ),
          1 ≤ N → 0 < eps → eps < eps₀ → 0 < lamStar → lamStar ≤ lam → lam ≤ 1 → θ ∈ angleBox N →
          θ ∈ tsupport (namedSelectorDerivative (constructedSelector d.thetaB η α) q) →
          ‖s-radialParameter d.theta eps‖ ≤ c*lamStar/(N:ℝ)^2 → ∀ i,
          ‖residueFactor (selectedContinuedRoot s
            (deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ lam θ i))‖ ≤
            selectedOneBodyBound d.thetaB η C eps (θ i) := by
  obtain ⟨CB,h,r,hCB,hh,hr,hbranch⟩ := protected_disk_branch_onebody d
  obtain ⟨ηA,hηA,hcoord⟩ := lowerChord_small_coordinate d.thetaB_pos d.thetaB_lt hh
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
  obtain ⟨cB,hcB,hB⟩ := hbranch τ hτ hτr
  obtain ⟨epsK,hepsK,_hepsK1,K,hK,hKD,hcover⟩ := current_regular_center_compact
    (c₀ := d.c₀) d.angle_relation hsinb hη hηsmall hα hαsmall hτ hτsmall hτS
  obtain ⟨cK,CK,hcK,hCK,hcompact⟩ := continuedRoot_compact_onebody hK hKD
  let c := min cB (min (1/4:ℝ) (cK/3))
  let eps₀ := min epsK (min r 1)
  let C := max CB CK
  have hc : 0 < c := lt_min hcB (lt_min (by norm_num) (by positivity))
  have hcB' : c ≤ cB := min_le_left _ _
  have hc1 : c ≤ 1/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hcK' : c ≤ cK/3 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨C,c,eps₀,lt_of_lt_of_le hCB (le_max_left _ _),hc,lt_min hepsK (lt_min hr zero_lt_one),?_⟩
  intro N eps lamStar lam θ q s hN heps hepslt hls hl hl1 hθ hsupport hsd i
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
  have hl0 : 0 ≤ lam := hls.le.trans hl
  have hn2 : 1 ≤ (N:ℝ)^2 := by nlinarith
  have hradius : c*lamStar/(N:ℝ)^2 ≤ c :=
    (div_le_self (by positivity) hn2).trans (mul_le_of_le_one_right hc.le (hl.trans hl1))
  have hP : 1 ≤ P := occupancy_named (fun i => hp0 (θ i)) q hqp
  have hPN : P ≤ N := occupancy_le (fun i => hp1 (θ i))
  have hρ0 : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hρ1 : ρ ≤ 1 := (div_le_one hn0).mpr hPN
  by_cases hcore : lowerChord d.thetaB (θ i) < η^2/2
  · simp only [selectedOneBodyBound,hcore,ite_true]
    have hch : lowerChord d.thetaB (θ i) ≤ η^2 := by linarith [sq_nonneg η]
    obtain ⟨hmi,hpi⟩ := constructed_lower_core_plateau hsinb hη hηsmall hα hch
    let u := θ i+d.thetaB-2*Real.pi
    have hu : |u| < h := hcoord (θ i) (hθ.1 i) (hθ.2 i)
      (hch.trans (pow_le_pow_left₀ hη.le hηA' 2))
    have hyp : y i=plateauY d.c₀ eps τ (lam*P/(N:ℝ)) d.thetaB u :=
      deformedPoint_current_plateau f d.thetaB d.c₀ eps τ lam θ i hpi hmi
    have hsB := hsd.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcB' hls.le) (sq_nonneg (N:ℝ)))
    have hbnd := hB N eps lamStar lam P u s hN heps hepsr hls hl hl1 hP hPN hu hsB
    change ‖residueFactor (selectedContinuedRoot s (y i))‖ ≤ _
    rw [hyp]
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
      have hh' : c*lamStar/(N:ℝ)^2 ≤ c := hradius
      linarith only [hsd,hh',hc1]
    have hnorm : 1 ≤ ‖radialParameter d.theta eps‖ := by rw [radialParameter_norm heps.le]; linarith
    have hsn := norm_ge_half_of_near_unit hnorm hsmall
    have hdiff : ‖W-W₀‖ ≤ cK := by
      have he : W-W₀=sourceS s-sourceS (radialParameter d.theta eps) := by dsimp [W,W₀,sourceW]; ring
      rw [he]
      have htrace := sourceS_sub_norm_le hsn hnorm
      have hcN : c*lamStar/(N:ℝ)^2 ≤ c := hradius
      linarith only [htrace,hsd,hcN,hcK']
    exact ((hcompact W₀ hW₀ W hdiff).1).trans (le_max_right CB CK)

end
end IsingBulk.Tail
