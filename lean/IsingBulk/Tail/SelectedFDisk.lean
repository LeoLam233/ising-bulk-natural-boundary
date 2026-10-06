import IsingBulk.Tail.SelectedFDiskSupport
import IsingBulk.Tail.RootInflation

/-! Constructed c/N selected-F root domain and global product gaps for the
actual coupled contour. Constants precede N, epsilon and every angular point.
Compact roots may leave the unit disk; their total inflation is paid by the
named inward-shifted upper root. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter Metric
open scoped Topology BigOperators

set_option maxHeartbeats 2000000 in
theorem selected_actual_root_disk (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ η₀ τ₀ : ℝ, 0 < η₀ ∧ 0 < τ₀ ∧
      ∀ η α τ : ℝ, 0 < η → η < η₀ → 0 < α → α < Real.sin d.thetaB/4 →
        0 < τ → τ < τ₀ → ∃ c eps₀ a : ℝ, 0 < c ∧ 0 < eps₀ ∧ 0 < a ∧
        ∀ (N : ℕ) (eps : ℝ) (θ : Fin N → ℝ) (s : ℂ),
          1 ≤ N → 0 < eps → eps < eps₀ → θ ∈ angleBox N →
          θ ∈ tsupport (fun θ : Fin N → ℝ => 1-angularSelector (constructedSelector d.thetaB η α) θ) →
          ‖s-radialParameter d.theta eps‖ ≤ c/(N:ℝ) →
          s ≠ 0 ∧
          (∀ i, sourceW s (deformedPoint (constructedSelector d.thetaB η α)
            (Real.exp (-d.c₀*eps)) τ 1 θ i) ∈ continuedRootDomain) ∧
          ‖coordinateProduct (fun i => selectedContinuedRoot s
            (deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ 1 θ i))‖ ≤
              Real.exp (-a) ∧
          ‖coordinateProduct (deformedPoint (constructedSelector d.thetaB η α)
            (Real.exp (-d.c₀*eps)) τ 1 θ)‖ ≤ Real.exp (-3*τ/2) := by
  obtain ⟨b,r,hb,hr,hbranch⟩ := selected_disk_true_branch d
  obtain ⟨ηA,hηA,hcoord⟩ := lowerChord_small_coordinate d.thetaB_pos d.thetaB_lt hr
  have hsinb : 0 < Real.sin d.thetaB := d.a_pos
  have hsint : 0 < Real.sin d.theta := Real.sin_pos_of_pos_of_lt_pi d.theta_pos
    (by linarith [Real.pi_pos,d.theta_lt])
  have hS : 0 < 1+Real.cos d.thetaB := by
    have hh := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos,d.theta_pos],d.theta_lt⟩
    linarith [d.angle_relation]
  let η₀ := min ηA (Real.sin d.thetaB/4)
  let τ₀ := min r (min (1/2:ℝ) ((1+Real.cos d.thetaB)/8))
  refine ⟨η₀,τ₀,lt_min hηA (by positivity),lt_min hr (lt_min (by norm_num) (by positivity)),?_⟩
  intro η α τ hη hηlt hα hαsmall hτ hτlt
  have hηsmall : η ≤ Real.sin d.thetaB/4 := hηlt.le.trans (min_le_right _ _)
  have hηA' : η ≤ ηA := hηlt.le.trans (min_le_left _ _)
  have hτr : τ < r := hτlt.trans_le (min_le_left _ _)
  have hτsmall : 2*τ ≤ 1 := by
    have hh := hτlt.le.trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hτS : 4*τ < 1+Real.cos d.thetaB := by
    have hh := hτlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  obtain ⟨cB,hcB,hB⟩ := hbranch τ hτ hτr
  obtain ⟨epsK,hepsK,hepsK1,K,hK,hKD,hcoverK⟩ :=
    selected_regular_center_compact (c₀ := d.c₀) d.angle_relation hsinb hη hηsmall hα hαsmall hτ hτsmall hτS
  obtain ⟨cI,L,hcI,hL,hprod⟩ := continuedRoot_compact_branch_product hK hKD
  obtain ⟨a,ha,hanchor⟩ := upper_anchor_exponential_attenuation d.theta d.c₀_pos.le hτ hα hsint.le
  obtain ⟨epsR,hepsR,hepsR1,hmargin⟩ := radialDampingMargin_linear hsint hcsmall
  let c := min cB (min (1/4:ℝ) (min (cI/3) (a/(6*L))))
  let eps₀ := min epsK (min epsR (min r 1))
  have hc : 0 < c := lt_min hcB (lt_min (by norm_num) (lt_min (by positivity) (by positivity)))
  have hcB' : c ≤ cB := min_le_left _ _
  have hcquarter : c ≤ 1/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hcI' : c ≤ cI/3 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hca : c ≤ a/(6*L) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have heps₀ : 0 < eps₀ := lt_min hepsK (lt_min hepsR (lt_min hr zero_lt_one))
  refine ⟨c,eps₀,a/2,hc,heps₀,half_pos ha,?_⟩
  intro N eps θ s hN heps hepslt hθ hsupport hsd
  let f := constructedSelector d.thetaB η α
  let R := Real.exp (-d.c₀*eps)
  let P := occupancy (fun i => f.p (θ i))
  let ρ := P/(N:ℝ)
  let y := deformedPoint f R τ 1 θ
  let W₀ : Fin N → ℂ := fun i => sourceW (radialParameter d.theta eps) (y i)
  let W : Fin N → ℂ := fun i => sourceW s (y i)
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0:ℝ) < N := by linarith
  have hepsK' : eps ≤ epsK := hepslt.le.trans (min_le_left _ _)
  have hepsR' : eps < epsR := hepslt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hepsr : eps < r := hepslt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have heps1 : eps ≤ 1 := hepslt.le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hp0 : ∀ x, 0 ≤ f.p x := fun x => (thresholdStep_range _ _ _).1
  have hp1 : ∀ x, f.p x ≤ 1 := fun x => (thresholdStep_range _ _ _).2
  have hm0 : ∀ x, 0 ≤ f.m x := fun x => Real.smoothTransition.nonneg _
  have hm1 : ∀ x, f.m x ≤ 1 := fun x => Real.smoothTransition.le_one _
  have hps : ∀ x, Real.sin x ≤ 0 → f.p x=0 := by
    intro x hx
    exact thresholdStep_zero (by linarith) (by linarith)
  have hms : ∀ x, 0 ≤ Real.sin x → f.m x=0 :=
    fun x hx => lowerM_zero_of_nonneg_sine d.thetaB η x hsinb hη hηsmall hx
  obtain ⟨q,hq⟩ := selected_tsupport_named f θ hsupport
  obtain ⟨hqp,hqm,hqsin,hqch⟩ := constructed_named_support hsinb hη hηsmall hα hq
  have hP : 1 ≤ P := occupancy_named (fun i => hp0 (θ i)) q hqp
  have hPN : P ≤ N := occupancy_le (fun i => hp1 (θ i))
  have hρ0 : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hρ1 : ρ ≤ 1 := (div_le_one hn0).mpr hPN
  have hyform (i : Fin N) : y i =
      radialAnglePoint (-d.c₀*eps+selectedLimitingShift f τ ρ (θ i)) (θ i) :=
    deformedPoint_selected_formula f d.c₀ eps τ θ i
  have hWform (i : Fin N) : W₀ i = selectedCenterW d.theta d.c₀ f τ eps ρ (θ i) := by
    change sourceW _ (y i) = _
    rw [hyform]
    rfl
  have hcompact (i : Fin N) (hi : η^2/2 ≤ lowerChord d.thetaB (θ i)) : W₀ i ∈ K := by
    rw [hWform]
    exact hcoverK eps heps.le hepsK' (ρ,θ i) ⟨⟨hρ0,hρ1⟩,⟨⟨hθ.1 i,hθ.2 i⟩,hi⟩⟩
  have hR : 0 < R := Real.exp_pos _
  have hR1 : R < 1 := by rw [Real.exp_lt_one_iff]; nlinarith [mul_pos d.c₀_pos heps]
  have hmargin' : R⁻¹-R < (sourceS (radialParameter d.theta eps)).im := by
    have hh := radialRadius_parameter_margin heps (hmargin eps heps hepsR')
    change R⁻¹-R+Real.sin d.theta*eps < _ at hh
    linarith [mul_pos hsint heps]
  have hcenter : ∀ i, 0 < (W₀ i).im := by
    intro i
    exact (sourceW_upper_of_margin hR hR1 hmargin' (deformedPoint_zero_norm f hR.le τ θ i)).trans_le
      (deformed_sourceW_im_ge (by omega) f hR hτ.le (by norm_num) θ _ hp0 hm0 hps hms i)
  have hsmall : ‖s-radialParameter d.theta eps‖ < (1:ℝ)/2 := by
    have hh : c/(N:ℝ) ≤ c := div_le_self hc.le hn
    linarith
  have hnorm : 1 ≤ ‖radialParameter d.theta eps‖ := by rw [radialParameter_norm heps.le]; linarith
  have hsn := norm_ge_half_of_near_unit hnorm hsmall
  have hs : s ≠ 0 := norm_pos_iff.mp (by linarith)
  have hdiff : ∀ i, ‖W i-W₀ i‖ ≤ 3*c/(N:ℝ) := by
    intro i
    have he : W i-W₀ i=sourceS s-sourceS (radialParameter d.theta eps) := by dsimp [W,W₀,sourceW]; ring
    rw [he]
    have hh := sourceS_sub_norm_le hsn hnorm
    calc
      _ ≤ 3*‖s-radialParameter d.theta eps‖ := hh
      _ ≤ 3*(c/(N:ℝ)) := mul_le_mul_of_nonneg_left hsd (by norm_num)
      _ = _ := by ring
  have hcover : ∀ i, W₀ i ∈ K ∨ 0 < (W i).im := by
    intro i
    by_cases hi : η^2/2 ≤ lowerChord d.thetaB (θ i)
    · exact Or.inl (hcompact i hi)
    · have hch : lowerChord d.thetaB (θ i) ≤ η^2 := by linarith [sq_nonneg η]
      obtain ⟨hmi,hpi⟩ := constructed_lower_core_plateau hsinb hη hηsmall hα hch
      let u := θ i+d.thetaB-2*Real.pi
      have hu : |u| < r := by
        apply hcoord (θ i) (hθ.1 i) (hθ.2 i)
        exact hch.trans (pow_le_pow_left₀ hη.le hηA' 2)
      have hyp : y i=plateauY d.c₀ eps τ ρ d.thetaB u :=
        deformedPoint_selected_plateau f d.thetaB d.c₀ eps τ θ i hpi hmi
      have hsB : ‖s-radialParameter d.theta eps‖ ≤ cB/(N:ℝ) :=
        hsd.trans (div_le_div_of_nonneg_right hcB' hn0.le)
      have hbnd := (hB N eps P u s hN heps hepsr hP hPN hu hsB).1
      refine Or.inr ?_
      change 0 < (sourceW s (y i)).im
      rw [hyp]
      exact lt_of_lt_of_le (by positivity : 0 < b*(eps+τ*ρ)) hbnd
  have hqK : W₀ q ∈ K := hcompact q hqch
  have hqnorm : ‖continuedRoot (W₀ q)‖ ≤ Real.exp (-a) := by
    rw [continuedRoot_eq_interiorRoot (hcenter q)]
    change ‖globalRoot (radialParameter d.theta eps) (y q)‖ ≤ _
    have hyq : y q=upperAnchorY d.c₀ eps τ 1 (θ q) := deformedPoint_selected_anchor f d.c₀ eps τ θ q hqp hqm
    rw [hyq]
    simpa only [mul_one] using hanchor eps 1 (θ q) heps.le heps1 (by norm_num) le_rfl hqsin
  have hd0 : 0 ≤ 3*c/(N:ℝ) := by positivity
  have hdI : 3*c/(N:ℝ) ≤ cI := by
    have hh : 3*c/(N:ℝ) ≤ 3*c := div_le_self (by positivity) hn
    linarith
  obtain ⟨hdom,hZ⟩ := hprod N W₀ W q a (3*c/(N:ℝ)) hd0 hdI hcenter hcover hdiff hqK hqnorm
  have hZa : ‖∏ i, continuedRoot (W i)‖ ≤ Real.exp (-(a/2)) := by
    apply hZ.trans
    apply Real.exp_le_exp.mpr
    have hca' := (le_div_iff₀ (by positivity : 0 < 6*L)).mp hca
    have he : (N:ℝ)*L*(3*c/(N:ℝ))=3*L*c := by field_simp
    rw [he]
    nlinarith only [hca']
  have hY : ‖coordinateProduct y‖ ≤ Real.exp (-3*τ/2) := by
    rw [deformed_product_norm f hR.le]
    have hsum := sum_retractionShift_le (by omega : 0<N) hτ.le (fun i => hp0 (θ i)) (fun i => hm1 (θ i))
    have hrpow : R^N ≤ 1 := pow_le_one₀ hR.le hR1.le
    have hexp : Real.exp (1*∑ i, retractionShift τ (fun j => f.p (θ j)) (fun j => f.m (θ j)) i) ≤ Real.exp (-3*τ/2) := by
      apply Real.exp_le_exp.mpr
      simp only [one_mul]
      nlinarith
    exact (mul_le_of_le_one_left (Real.exp_pos _).le hrpow).trans hexp
  exact ⟨hs,hdom,hZa,hY⟩

end
end IsingBulk.Tail
