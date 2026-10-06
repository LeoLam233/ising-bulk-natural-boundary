import IsingBulk.Tail.SelectedFDensityEstimate
import IsingBulk.Tail.SelectedGlobalEnvelope
import IsingBulk.Tail.SelectedFDisk
import IsingBulk.Tail.SelectedYKernel

/-! Actual selected contour density after compact Gaussian discount. All
constants are chosen before the number of particles and radial parameter. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem selected_actual_reduced_discount (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ η₀ τ₀ : ℝ, 0 < η₀ ∧ 0 < τ₀ ∧
      ∀ η α τ : ℝ, 0 < η → η < η₀ → 0 < α → α < Real.sin d.thetaB/4 →
        0 < τ → τ < τ₀ → ∃ c eps₀ C D K a : ℝ,
        0 < c ∧ 0 < eps₀ ∧ 0 < C ∧ 0 < D ∧ 0 < K ∧ 0 < a ∧
        ∀ (N : ℕ) (eps L : ℝ) (θ : Fin N → ℝ) (s : ℂ),
          1 ≤ N → 0 < eps → eps < eps₀ → 0 < L → θ ∈ angleBox N →
          θ ∈ tsupport (fun θ : Fin N → ℝ => 1-angularSelector (constructedSelector d.thetaB η α) θ) →
          ‖s-radialParameter d.theta eps‖ ≤ c/(N:ℝ) →
          let y := deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ 1 θ
          ‖canceledReducedDensity (fun i => selectedContinuedRoot s (y i)) y‖ ≤
            K*D^N*Real.exp ((Real.log L)^2/(4*a))*
              ((∏ i, discountedSelectedWeight d.thetaB η C eps L (θ i))*‖First.pairProduct y‖) := by
  obtain ⟨ηR,τR,hηR,hτR,hR⟩ := selected_actual_root_disk d hcsmall
  obtain ⟨ηP,τP,hηP,hτP,hP⟩ := selected_actual_root_pair_product d hcsmall
  obtain ⟨ηV,τV,hηV,hτV,hV⟩ := selected_actual_onebody_bound d
  refine ⟨min ηR (min ηP (min ηV (Real.sin d.thetaB/4))),min τR (min τP τV),
    lt_min hηR (lt_min hηP (lt_min hηV (by positivity [d.a_pos]))),
    lt_min hτR (lt_min hτP hτV),?_⟩
  intro η α τ hη hηlt hα hαsmall hτ hτlt
  have hηr := hηlt.trans_le (min_le_left _ _)
  have hηp := hηlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hηv := hηlt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hηsmall : η ≤ Real.sin d.thetaB/4 := hηlt.le.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨cR,eR,aR,hcR,heR,haR,hroot⟩ := hR η α τ hη hηr hα hαsmall hτ (hτlt.trans_le (min_le_left _ _))
  obtain ⟨cP,eP,B,a,hcP,heP,hB,ha,hpair⟩ := hP η α τ hη hηp hα hαsmall hτ
    (hτlt.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨C,cV,eV,hC,hcV,heV,hvertex⟩ := hV η α τ hη hηv hα hαsmall hτ
    (hτlt.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  let c := min cR (min cP (min cV (1/4:ℝ)))
  let e := min eR (min eP (min eV 1))
  let A := 21+4*Real.exp (d.c₀+2*τ)
  let gZ := 1-Real.exp (-aR)
  let gY := 1-Real.exp (-3*τ/2)
  have hgZ : 0 < gZ := by dsimp [gZ]; have := Real.exp_lt_one_iff.mpr (neg_neg_of_pos haR); linarith
  have hgY : 0 < gY := by dsimp [gY]; have := Real.exp_lt_one_iff.mpr (by linarith : -3*τ/2<0); linarith
  refine ⟨c,e,C,A*B,2/(gZ*gY),a,
    lt_min hcR (lt_min hcP (lt_min hcV (by norm_num))),
    lt_min heR (lt_min heP (lt_min heV (by norm_num))),hC,by dsimp [A]; positivity,
    by positivity,ha,?_⟩
  intro N eps L θ s hN heps hepslt hL hθ hsupp hsd
  have hcn : 0 ≤ (N:ℝ) := Nat.cast_nonneg _
  have hdR := hsd.trans (div_le_div_of_nonneg_right (min_le_left cR _) hcn)
  have hdP := hsd.trans (div_le_div_of_nonneg_right
    ((min_le_right cR _).trans (min_le_left cP _)) hcn)
  have hdV := hsd.trans (div_le_div_of_nonneg_right
    ((min_le_right cR _).trans ((min_le_right cP _).trans (min_le_left cV _))) hcn)
  have heR' := hepslt.trans_le (min_le_left eR _)
  have heP' := hepslt.trans_le ((min_le_right eR _).trans (min_le_left eP _))
  have heV' := hepslt.trans_le ((min_le_right eR _).trans ((min_le_right eP _).trans (min_le_left eV _)))
  have he1 : eps ≤ 1 := hepslt.le.trans ((min_le_right eR _).trans ((min_le_right eP _).trans (min_le_right eV _)))
  have hc1 : c ≤ 1/4 := (min_le_right cR _).trans ((min_le_right cP _).trans (min_le_right cV _))
  obtain ⟨_,hW,hZ,hY⟩ := hroot N eps θ s hN heps heR' hθ hsupp hdR
  let f := constructedSelector d.thetaB η α
  let y := deformedPoint f (Real.exp (-d.c₀*eps)) τ 1 θ
  have hy0 : ∀ i, y i ≠ 0 := by
    intro i
    dsimp [y,deformedPoint]
    exact mul_ne_zero (by exact_mod_cast (Real.exp_pos (-d.c₀*eps)).ne') (Complex.exp_ne_zero _)
  have hygap : ∀ i j, 1-y i*y j ≠ 0 := selected_y_pair_denominator_ne_zero (by omega)
    d.thetaB η α d.a_pos hη hηsmall hα hαsmall (Real.exp_nonneg _)
    (Real.exp_lt_one_iff.mpr (by nlinarith [d.c₀_pos])) hτ θ
  have hn := selected_actual_inverse_numerator hN f d.c₀_pos.le hτ.le heps.le he1 hc1
    (fun x => (thresholdStep_range _ _ _).1) (fun x => (thresholdStep_range _ _ _).2)
    (fun x => Real.smoothTransition.nonneg _) (fun x => Real.smoothTransition.le_one _) θ hsd
  have hzGap : gZ ≤ ‖1-coordinateProduct (fun i => selectedContinuedRoot s (y i))‖ := by
    have hh := norm_sub_norm_le (1:ℂ) (coordinateProduct (fun i => selectedContinuedRoot s (y i)))
    simp only [norm_one] at hh
    dsimp [gZ]
    linarith
  have hyGap : gY ≤ ‖1-coordinateProduct y‖ := by
    have hh := norm_sub_norm_le (1:ℂ) (coordinateProduct y)
    simp only [norm_one] at hh
    dsimp [gY]
    linarith
  dsimp only
  rw [canceledReducedDensity_continued_eq s y hy0 hW hygap]
  have hh := reducedDensity_discounted_bound (fun i => selectedContinuedRoot s (y i)) y
    d.thetaB η C eps θ (A := A) (by dsimp [A]; positivity) hB.le hC.le hgZ hgY ha hL hn hzGap hyGap
    (hpair N eps θ s hN heps heP' hθ hsupp hdP) (hvertex N eps θ s hN heps heV' hθ hsupp hdV)
  convert hh using 1
  ring

end
end IsingBulk.Tail
