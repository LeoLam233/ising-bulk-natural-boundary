import IsingBulk.Tail.SelectedFDensityEstimate
import IsingBulk.Tail.CurrentGlobalEnvelope
import IsingBulk.Tail.ProtectedActualOneBody
import IsingBulk.Tail.ProtectedRootPairProduct
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

theorem protected_actual_reduced_discount (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ η₀ τ₀ : ℝ, 0 < η₀ ∧ 0 < τ₀ ∧
      ∀ η α τ : ℝ, 0 < η → η < η₀ → 0 < α → α < Real.sin d.thetaB/4 →
        0 < τ → τ < τ₀ → ∃ c eps₀ C D K a : ℝ,
        0 < c ∧ 0 < eps₀ ∧ 0 < C ∧ 0 < D ∧ 0 < K ∧ 0 < a ∧
        ∀ (N : ℕ) (eps L lamStar lam : ℝ) (θ : Fin N → ℝ) (qidx : Fin N) (s : ℂ),
          1 ≤ N → 0 < eps → eps < eps₀ → 0 < L → 0 < lamStar → lamStar ≤ lam → lam ≤ 1 → θ ∈ angleBox N →
          θ ∈ tsupport (namedSelectorDerivative (constructedSelector d.thetaB η α) qidx) →
          ‖s-radialParameter d.theta eps‖ ≤ c*lamStar/(N:ℝ)^2 →
          let y := deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ lam θ
          ‖canceledReducedDensity (fun i => selectedContinuedRoot s (y i)) y‖ ≤
            (K/lam^2)*D^N*Real.exp ((Real.log L)^2/(4*a))*
              ((∏ i, discountedSelectedWeight d.thetaB η C eps L (θ i))*‖First.pairProduct y‖) := by
  obtain ⟨ηR,τR,hηR,hτR,hR⟩ := constructed_current_actual_root_disk d hcsmall
  obtain ⟨ηP,τP,hηP,hτP,hP⟩ := protected_actual_root_pair_product d hcsmall
  obtain ⟨ηV,τV,hηV,hτV,hV⟩ := protected_actual_onebody_bound d
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
  let gZ := aR*Real.exp (-aR)
  let gY := (3*τ/2)*Real.exp (-(3*τ/2))
  have hgZ : 0 < gZ := by dsimp [gZ]; positivity
  have hgY : 0 < gY := by dsimp [gY]; positivity
  have hc0 : 0 < c := lt_min hcR (lt_min hcP (lt_min hcV (by norm_num)))
  refine ⟨c,e,C,A*B,2/(gZ*gY),a,
    lt_min hcR (lt_min hcP (lt_min hcV (by norm_num))),
    lt_min heR (lt_min heP (lt_min heV (by norm_num))),hC,by dsimp [A]; positivity,
    by positivity,ha,?_⟩
  intro N eps L lamStar lam θ qidx s hN heps hepslt hL hls hl hl1 hθ hsupp hsd
  have hlam : 0 < lam := hls.trans_le hl
  have hcn : 0 ≤ (N:ℝ)^2 := sq_nonneg _
  have hdR := hsd.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (min_le_left cR _) hls.le) hcn)
  have hdP := hsd.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right ((min_le_right cR _).trans (min_le_left cP _)) hls.le) hcn)
  have hdV := hsd.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right ((min_le_right cR _).trans ((min_le_right cP _).trans (min_le_left cV _))) hls.le) hcn)
  have heR' := hepslt.trans_le (min_le_left eR _)
  have heP' := hepslt.trans_le ((min_le_right eR _).trans (min_le_left eP _))
  have heV' := hepslt.trans_le ((min_le_right eR _).trans ((min_le_right eP _).trans (min_le_left eV _)))
  have he1 : eps ≤ 1 := hepslt.le.trans ((min_le_right eR _).trans ((min_le_right eP _).trans (min_le_right eV _)))
  have hc1 : c ≤ 1/4 := (min_le_right cR _).trans ((min_le_right cP _).trans (min_le_right cV _))
  obtain ⟨_,hW,hZ,hY⟩ := hroot N eps lamStar lam θ qidx s hN heps heR' hls hl hl1 hθ hsupp hdR
  let f := constructedSelector d.thetaB η α
  let y := deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ
  have hy0 : ∀ i, y i ≠ 0 := by
    intro i
    dsimp [y,deformedPoint]
    exact mul_ne_zero (by exact_mod_cast (Real.exp_pos (-d.c₀*eps)).ne') (Complex.exp_ne_zero _)
  have hygap : ∀ i j, 1-y i*y j ≠ 0 := by
    have he : y=deformedPoint f (Real.exp (-d.c₀*eps)) (lam*τ) 1 θ :=
      funext (deformedPoint_scale_lambda f _ τ lam θ)
    rw [he]
    exact selected_y_pair_denominator_ne_zero (by omega)
      d.thetaB η α d.a_pos hη hηsmall hα hαsmall (Real.exp_nonneg _)
      (Real.exp_lt_one_iff.mpr (by nlinarith [d.c₀_pos])) (mul_pos hlam hτ) θ
  have hn := current_actual_inverse_numerator hN f d.c₀_pos.le hτ.le heps.le he1 hc0.le hc1
    hls.le hl hl1 (fun x => (thresholdStep_range _ _ _).1) (fun x => (thresholdStep_range _ _ _).2)
    (fun x => Real.smoothTransition.nonneg _) (fun x => Real.smoothTransition.le_one _) θ hsd
  have hzGap : gZ*lam ≤ ‖1-coordinateProduct (fun i => selectedContinuedRoot s (y i))‖ :=
    exponential_attenuation_linear_gap haR.le hlam.le hl1 hZ
  have hyGap : gY*lam ≤ ‖1-coordinateProduct y‖ :=
    exponential_attenuation_linear_gap (by positivity : 0≤3*τ/2) hlam.le hl1 hY
  dsimp only
  rw [canceledReducedDensity_continued_eq s y hy0 hW hygap]
  have hh := reducedDensity_discounted_bound (fun i => selectedContinuedRoot s (y i)) y
    d.thetaB η C eps θ (A := A) (by dsimp [A]; positivity) hB.le hC.le (mul_pos hgZ hlam) (mul_pos hgY hlam) ha hL hn hzGap hyGap
    (hpair N eps lamStar lam θ qidx s hN heps heP' hls hl hl1 hθ hsupp hdP) (hvertex N eps lamStar lam θ qidx s hN heps heV' hls hl hl1 hθ hsupp hdV)
  dsimp only [y,f] at hh
  convert hh using 1
  field_simp

end
end IsingBulk.Tail
