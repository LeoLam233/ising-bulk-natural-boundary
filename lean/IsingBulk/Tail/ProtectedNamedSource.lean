import IsingBulk.Tail.ProtectedCurrentEnvelope

/-! Every clause of the named-support protected disk lemma, with a single
common tuple of constants and the literal constructed coupled density. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Metric MeasureTheory
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

theorem protected_named_source (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) :
    ∃ η₀ : ℝ, 0<η₀ ∧ ∀ η : ℝ, 0<η → η<η₀ →
      ∃ α₀ τ₀ : ℝ, 0<α₀ ∧ 0<τ₀ ∧ ∀ α τ : ℝ,
        0<α → α<α₀ → 0<τ → τ<τ₀ →
        ∃ c eps₀ g C B κ : ℝ, 0<c ∧ 0<eps₀ ∧ 0<g ∧ 0<C ∧ 0<B ∧ 0<κ ∧
          ∀ (N : ℕ) (eps lamStar lam : ℝ) (θ : Fin N → ℝ) (q : Fin N) (s : ℂ),
            1≤N → 0<eps → eps<eps₀ → 0<lamStar → lamStar≤lam → lam≤1 →
            θ ∈ angleBox N → θ ∈ tsupport (namedSelectorDerivative (constructedSelector d.thetaB η α) q) →
            ‖s-radialParameter d.theta eps‖≤c*lamStar/(N:ℝ)^2 →
            let f := constructedSelector d.thetaB η α
            let r := Real.exp (-d.c₀*eps)
            let y := deformedPoint f r τ lam θ
            let z := fun i => selectedContinuedRoot s (y i)
            AnalyticAt ℂ (fun v => continuedNamedCurrentDensity f r τ lam v q θ) s ∧
            g*lam≤‖1-coordinateProduct z‖ ∧ g*lam≤‖1-coordinateProduct y‖ ∧
            ‖canceledPairProduct z y‖≤B^N*Real.exp (-κ*(N:ℝ)^2) ∧
            (∀ i, ‖residueFactor (z i)‖≤selectedOneBodyBound d.thetaB η C eps (θ i)) ∧
            IntegrableOn (fun x : Fin N → ℝ => ∏ i, selectedOneBodyBound d.thetaB η C eps (x i)) (angleBox N) ∧
            (∫ x in angleBox N, ∏ i, selectedOneBodyBound d.thetaB η C eps (x i))≤
              (4*C*Real.sqrt (2*Real.pi)+C*(2*Real.pi))^N := by
  obtain ⟨ηR,τR,hηR,hτR,hR⟩ := constructed_current_actual_root_disk d hcsmall
  obtain ⟨ηV,τV,hηV,hτV,hV⟩ := protected_actual_onebody_bound d
  obtain ⟨ηP,hηP,hP⟩ := protected_actual_complete_pair_product d
  refine ⟨min ηP (min ηR (min ηV (Real.sin d.thetaB/4))),
    lt_min hηP (lt_min hηR (lt_min hηV (by positivity [d.a_pos]))),?_⟩
  intro η hη hηlt
  have hηp := hηlt.trans_le (min_le_left _ _)
  have hηr := hηlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hηv := hηlt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hηsmall : η≤Real.sin d.thetaB/4 := hηlt.le.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨αP,τP,hαP,hτP,hpairSetup⟩ := hP η hη hηp
  refine ⟨min αP (Real.sin d.thetaB/4),min τP (min τR τV),
    lt_min hαP (by positivity [d.a_pos]),lt_min hτP (lt_min hτR hτV),?_⟩
  intro α τ hα hαlt hτ hτlt
  have hαsmall := hαlt.trans_le (min_le_right _ _)
  obtain ⟨cP,eP,P,κ,hcP,heP,hPpos,hκ,hpair⟩ := hpairSetup α τ hα
    (hαlt.trans_le (min_le_left _ _)) hτ (hτlt.trans_le (min_le_left _ _))
  obtain ⟨cR,eR,aR,hcR,heR,haR,hroot⟩ := hR η α τ hη hηr hα hαsmall hτ
    (hτlt.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨C,cV,eV,hC,hcV,heV,hvertex⟩ := hV η α τ hη hηv hα hαsmall hτ
    (hτlt.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  let c := min cR (min cP cV)
  let e := min eR (min eP eV)
  let gZ := aR*Real.exp (-aR)
  let gY := (3*τ/2)*Real.exp (-(3*τ/2))
  have hgZ : 0<gZ := by dsimp [gZ]; positivity
  have hgY : 0<gY := by dsimp [gY]; positivity
  let g := min gZ gY
  refine ⟨c,e,g,C,P,κ,lt_min hcR (lt_min hcP hcV),lt_min heR (lt_min heP heV),
    lt_min hgZ hgY,hC,hPpos,hκ,?_⟩
  intro N eps lamStar lam θ q s hN heps hepslt hls hl hl1 hθ hsupp hsd
  have hlam : 0<lam := hls.trans_le hl
  have hdR := hsd.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (min_le_left cR _) hls.le) (sq_nonneg (N:ℝ)))
  have hdP := hsd.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right ((min_le_right cR _).trans (min_le_left cP cV)) hls.le) (sq_nonneg (N:ℝ)))
  have hdV := hsd.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right ((min_le_right cR _).trans (min_le_right cP cV)) hls.le) (sq_nonneg (N:ℝ)))
  have heR' := hepslt.trans_le (min_le_left eR _)
  have heP' := hepslt.trans_le ((min_le_right eR _).trans (min_le_left eP eV))
  have heV' := hepslt.trans_le ((min_le_right eR _).trans (min_le_right eP eV))
  let f := constructedSelector d.thetaB η α
  let r := Real.exp (-d.c₀*eps)
  let y := deformedPoint f r τ lam θ
  let z := fun i => selectedContinuedRoot s (y i)
  obtain ⟨hs,hW,hZ,hY⟩ := hroot N eps lamStar lam θ q s hN heps heR' hls hl hl1 hθ hsupp hdR
  have hzGap : g*lam≤‖1-coordinateProduct z‖ :=
    (mul_le_mul_of_nonneg_right (min_le_left gZ gY) hlam.le).trans
      (exponential_attenuation_linear_gap haR.le hlam.le hl1 hZ)
  have hyGap : g*lam≤‖1-coordinateProduct y‖ :=
    (mul_le_mul_of_nonneg_right (min_le_right gZ gY) hlam.le).trans
      (exponential_attenuation_linear_gap (by positivity : 0≤3*τ/2) hlam.le hl1 hY)
  have hgp : 0<g*lam := mul_pos (lt_min hgZ hgY) hlam
  have hz0 : 1-coordinateProduct z≠0 := norm_pos_iff.mp (hgp.trans_le hzGap)
  have hy0 : 1-coordinateProduct y≠0 := norm_pos_iff.mp (hgp.trans_le hyGap)
  refine ⟨?_,hzGap,hyGap,?_,?_,?_⟩
  · exact continuedNamedCurrentDensity_analyticAt f (Real.exp_pos _).ne' τ lam θ q hs hW hy0 hz0
  · exact hpair N eps lamStar lam θ q s hN heps heP' hls hl hl1 hθ hsupp hdP
  · exact hvertex N eps lamStar lam θ q s hN heps heV' hls hl hl1 hθ hsupp hdV
  · exact selectedOneBodyBound_product_integral N d.thetaB_pos.le
      (by linarith [d.thetaB_lt,Real.pi_pos]) hC.le heps

end
end IsingBulk.Tail
