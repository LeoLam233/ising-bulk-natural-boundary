import IsingBulk.HT.Contour.OnsiteGaussianIntegration
import IsingBulk.HT.Lie.OnsiteCurrentPointwise
import IsingBulk.HT.Lie.OnsiteOriginalPointwise

/-! Actual all-N onsite sector Gaussian integrals. The parameter radius is
fixed, the full homotopy interval is retained, and every source/volume bound
is supplied by its proved physical endpoint rather than a certificate. -/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail IsingBulk.Lie IsingBulk.HT.Lie Set Filter MeasureTheory Metric
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- Original onsite lower sector, including the empty and full branch
assignments. The bound is uniform in the unused homotopy strength at lam=0. -/
theorem onsite_original_sector_derivative_gaussian (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) :
    ∃ η₀ : ℝ,0<η₀ ∧ ∀ η : ℝ,0<η → η<η₀ →
      ∃ α₀ κ : ℝ,0<α₀ ∧ 0<κ ∧ ∀ α : ℝ,0<α → α<α₀ →
      ∀ (order : ℕ) (cap : ℝ),0<cap →
      ∃ inner₀ : ℝ,0< inner₀ ∧ inner₀≤cap ∧ ∀ (inner : ℝ) (hi : 0< inner),inner≤ inner₀ →
      ∃ e C : ℝ,0<e ∧ 0<C ∧
      ∀ (n k : ℕ) (eps τ : ℝ) (sigma : Fin (n+1) → Fin 3),
      k≤order → 0<eps → eps<e → 0≤τ →
      ‖iteratedDeriv k (onsiteOriginalSectorIntegral (n+1) (constructedSelector d.thetaB η α)
        (Real.exp (-d.c₀*eps)) τ d.thetaB inner hi sigma) (radialParameter d.theta eps)‖≤
        C^(n+1)*((n+1:ℕ):ℝ)^(5*order)*Real.exp (-κ*((n+1:ℕ):ℝ)^2) := by
  obtain ⟨ηP,hηP,hPoint⟩ := onsite_original_real_weight_pointwise d hcsmall
  obtain ⟨CV,eV,tV,hCV,heV,htV,hVolume⟩ := onsite_actual_sector_volume_integrals d hcsmall
  obtain ⟨cL,eL,tL,hcL,_hcLsmall,heL,htL,hCover⟩ := onsite_sector_support_covers d hcsmall
  refine ⟨min ηP (Real.sin d.thetaB/4),lt_min hηP (by positivity [d.a_pos]),?_⟩
  intro η hη hηlt
  have hηsmall : η≤Real.sin d.thetaB/4 := hηlt.le.trans (min_le_right _ _)
  obtain ⟨αP,κ,hαP,hκ,hPoint⟩ := hPoint η hη (hηlt.trans_le (min_le_left _ _))
  refine ⟨min αP (Real.sin d.thetaB/4),κ,lt_min hαP (by positivity [d.a_pos]),hκ,?_⟩
  intro α hα hαlt order cap hcap
  have hαsmall : α<Real.sin d.thetaB/4 := hαlt.trans_le (min_le_right _ _)
  obtain ⟨innerP,hiP,hiPcap,hPoint⟩ := hPoint α hα (hαlt.trans_le (min_le_left _ _)) order cap hcap
  obtain ⟨innerV,hiV,hVolume⟩ := hVolume η α hη hηsmall hα hαsmall
  refine ⟨min innerP (min innerV ((Real.sin d.thetaB)^2/4)),
    lt_min hiP (lt_min hiV (by positivity [d.a_pos])),(min_le_left _ _).trans hiPcap,?_⟩
  intro inner hi hinner
  have hiP' : inner≤ innerP := hinner.trans (min_le_left _ _)
  have hiV' : inner≤ innerV := hinner.trans ((min_le_right _ _).trans (min_le_left _ _))
  have his : inner≤(Real.sin d.thetaB)^2/4 := hinner.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨cP,eP,CP,hcP,heP,hCP,hPoint⟩ := hPoint inner hi hiP'
  refine ⟨min eP (min eV eL),CP*CV,lt_min heP (lt_min heV heL),mul_pos hCP hCV,?_⟩
  intro n k eps τ sigma hk heps hepslt hτ
  let f := constructedSelector d.thetaB η α
  let r := Real.exp (-d.c₀*eps)
  let s := radialParameter d.theta eps
  let J := mixedBranchIndexSet sigma
  let w := onsiteOriginalSectorWeight f d.thetaB inner hi sigma
  have hf : RegularSelector f := constructedSelector_regular d.thetaB η α d.a_pos hη hηsmall hα
  have heP' : eps<eP := hepslt.trans_le (min_le_left _ _)
  have heV' : eps<eV := hepslt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have heL' : eps<eL := hepslt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hCoverK,_⟩ := hCover η α inner hη hηsmall hα hαsmall hi his n eps τ 0 0 sigma
    heps heL' hτ le_rfl zero_le_one (by simpa using htL)
  have hID := onsite_supported_periodic_lie_integral J f hf (Real.exp_pos _) τ 0 isOpen_ball w
    (onsiteOriginalSectorWeight_smooth f hf d.thetaB inner hi sigma)
    (onsiteOriginalSectorWeight_periodic f hf d.thetaB inner hi sigma) hCoverK
  obtain ⟨hvK,_⟩ := hVolume inner hi hiV' n eps τ 0 0 sigma heps heV' hτ le_rfl zero_le_one
    (by simpa using htV)
  let P := CP^(n+1)*((n+1:ℕ):ℝ)^(5*order)*Real.exp (-κ*((n+1:ℕ):ℝ)^2)
  have hbound := onsite_lie_integral_of_volume_bound J f r τ 0 w hID
    (mem_ball_self (mul_pos hcL heps)) k (P := P) (by dsimp [P]; positivity) hvK.1 hvK.2
    (by
      intro θ hθ
      apply hPoint n k eps τ θ 0 sigma s hk heps heP' hτ hθ.1
        (onsiteOriginalSectorWeight_support f d.thetaB inner hi sigma hθ.2)
      simp only [s,sub_self,norm_zero]
      exact (mul_pos hcP heps).le)
  apply hbound.trans_eq
  dsimp [P]
  simp only [mul_pow]
  ring

/-- Complete named onsite current, all lambda in [0,1]. The strength is
chosen after the fixed derivative order and geometry and before lambda. -/
theorem onsite_current_sector_derivative_gaussian (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) :
    ∃ η₀ : ℝ,0<η₀ ∧ ∀ η : ℝ,0<η → η<η₀ →
      ∃ α₀ : ℝ,0<α₀ ∧ ∀ α : ℝ,0<α → α<α₀ →
      ∀ (order : ℕ) (cap : ℝ),0<cap →
      ∃ inner₀ : ℝ,0< inner₀ ∧ inner₀≤cap ∧ ∀ (inner : ℝ) (hi : 0< inner),inner≤ inner₀ →
      ∃ τ₀ : ℝ,0<τ₀ ∧ ∀ τ : ℝ,0<τ → τ<τ₀ →
      ∃ κ e C : ℝ,0<κ ∧ 0<e ∧ 0<C ∧
      ∀ (n k : ℕ) (eps lam : ℝ) (q : Fin (n+1)) (sigma : Fin (n+1) → Fin 3),
      k≤order → 0<eps → eps<e → 0≤lam → lam≤1 →
      ‖iteratedDeriv k (onsiteNamedSectorIntegral (n+1) (constructedSelector d.thetaB η α)
        (Real.exp (-d.c₀*eps)) τ lam d.thetaB inner hi q sigma) (radialParameter d.theta eps)‖≤
        C^(n+1)*((n+1:ℕ):ℝ)^(5*order)*Real.exp (-κ*((n+1:ℕ):ℝ)^2) := by
  obtain ⟨ηP,hηP,hPoint⟩ := onsite_current_real_weight_pointwise d hcsmall
  obtain ⟨CV,eV,tV,hCV,heV,htV,hVolume⟩ := onsite_actual_sector_volume_integrals d hcsmall
  obtain ⟨cL,eL,tL,hcL,_hcLsmall,heL,htL,hCover⟩ := onsite_sector_support_covers d hcsmall
  refine ⟨min ηP (Real.sin d.thetaB/4),lt_min hηP (by positivity [d.a_pos]),?_⟩
  intro η hη hηlt
  have hηsmall : η≤Real.sin d.thetaB/4 := hηlt.le.trans (min_le_right _ _)
  obtain ⟨αP,hαP,hPoint⟩ := hPoint η hη (hηlt.trans_le (min_le_left _ _))
  refine ⟨min αP (Real.sin d.thetaB/4),lt_min hαP (by positivity [d.a_pos]),?_⟩
  intro α hα hαlt order cap hcap
  have hαsmall : α<Real.sin d.thetaB/4 := hαlt.trans_le (min_le_right _ _)
  obtain ⟨innerP,hiP,hiPcap,hPoint⟩ := hPoint α hα (hαlt.trans_le (min_le_left _ _)) order cap hcap
  obtain ⟨innerV,hiV,hVolume⟩ := hVolume η α hη hηsmall hα hαsmall
  refine ⟨min innerP (min innerV ((Real.sin d.thetaB)^2/4)),
    lt_min hiP (lt_min hiV (by positivity [d.a_pos])),(min_le_left _ _).trans hiPcap,?_⟩
  intro inner hi hinner
  have hiP' : inner≤ innerP := hinner.trans (min_le_left _ _)
  have hiV' : inner≤ innerV := hinner.trans ((min_le_right _ _).trans (min_le_left _ _))
  have his : inner≤(Real.sin d.thetaB)^2/4 := hinner.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨τP,hτP,hPoint⟩ := hPoint inner hi hiP'
  refine ⟨min τP (min tL (min tV 1)),lt_min hτP (lt_min htL (lt_min htV zero_lt_one)),?_⟩
  intro τ hτ hτlt
  have hτP' : τ<τP := hτlt.trans_le (min_le_left _ _)
  have hτL : τ<tL := hτlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hτV : τ<tV := hτlt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hτ1 : τ≤1 := hτlt.le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨κ,cP,eP,CP,hκ,hcP,heP,hCP,hPoint⟩ := hPoint τ hτ hτP'
  refine ⟨κ,min eP (min eV eL),2*(CP*CV),hκ,lt_min heP (lt_min heV heL),by positivity,?_⟩
  intro n k eps lam q sigma hk heps hepslt hl0 hl1
  let f := constructedSelector d.thetaB η α
  let r := Real.exp (-d.c₀*eps)
  let s := radialParameter d.theta eps
  let J := mixedBranchIndexSet sigma
  let w : (Fin (n+1) → ℝ) → ℂ := fun θ =>
    (namedSelectorDerivative f q θ*sectorAssignmentWeight d.thetaB inner hi sigma θ:ℝ)
  have hf : RegularSelector f := constructedSelector_regular d.thetaB η α d.a_pos hη hηsmall hα
  have htl : lam*τ≤τ := mul_le_of_le_one_left hτ.le hl1
  have heP' : eps<eP := hepslt.trans_le (min_le_left _ _)
  have heV' : eps<eV := hepslt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have heL' : eps<eL := hepslt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hsupReal : tsupport w=tsupport (fun θ =>
      namedSelectorDerivative f q θ*sectorAssignmentWeight d.thetaB inner hi sigma θ) :=
    onsite_real_weight_tsupport_eq _
  have hsup : tsupport w=tsupport (onsiteNamedSectorWeight f d.thetaB inner hi q sigma τ) := by
    rw [onsiteNamedSectorWeight_tsupport_eq f d.thetaB inner hi q sigma hτ.ne']
    exact hsupReal
  have hw : ContDiff ℝ ∞ w := Complex.ofRealCLM.contDiff.comp
    ((namedSelectorDerivative_smooth f hf q).mul (sector_assignment_smooth d.thetaB inner hi sigma))
  have hwper : CoordinatePeriodic (n+1) w := by
    intro θ i
    dsimp [w]
    rw [namedSelectorDerivative_periodic f hf,sectorAssignmentWeight_periodic]
  obtain ⟨_,hCoverS⟩ := hCover η α inner hη hηsmall hα hαsmall hi his n eps τ lam q sigma
    heps heL' hτ.le hl0 hl1 (htl.trans_lt hτL)
  have hcover : ball s (cL*eps) ×ˢ tsupport w⊆onsiteLieDomain J f r τ lam := by
    simpa only [hsup] using hCoverS
  have hID := onsite_supported_periodic_lie_integral J f hf (Real.exp_pos _) τ lam
    isOpen_ball w hw hwper hcover
  obtain ⟨_,hvS⟩ := hVolume inner hi hiV' n eps τ lam q sigma heps heV' hτ.le hl0 hl1 (htl.trans_lt hτV)
  rw [← hsup] at hvS
  let P := CP^(n+1)*((n+1:ℕ):ℝ)^(5*order)*Real.exp (-κ*((n+1:ℕ):ℝ)^2)
  have hreal := onsite_lie_integral_of_volume_bound J f r τ lam w hID
    (mem_ball_self (mul_pos hcL heps)) k (P := P) (by dsimp [P]; positivity) hvS.1 hvS.2
    (by
      intro θ hθ
      apply hPoint n k eps lam θ q sigma s hk heps heP' hl0 hl1 hθ.1
        (by
          change θ ∈ tsupport (fun x =>
            namedSelectorDerivative f q x*sectorAssignmentWeight d.thetaB inner hi sigma x)
          rw [← hsupReal]
          exact hθ.2)
      simp only [s,sub_self,norm_zero]
      exact (mul_pos hcP heps).le)
  have hreal' : ‖iteratedDeriv k (fun z => ∫ θ in angleBox (n+1),w θ*onsitePulledDensity f r τ lam z θ) s‖≤
      (CP*CV)^(n+1)*((n+1:ℕ):ℝ)^(5*order)*Real.exp (-κ*((n+1:ℕ):ℝ)^2) := by
    apply hreal.trans_eq
    dsimp [P]
    simp only [mul_pow]
    ring
  rw [onsiteNamedSectorIntegral_deriv_const,norm_mul]
  have hscalar : ‖-2*Complex.I*(τ:ℂ)‖≤2 := by
    simp only [norm_mul,norm_neg,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hτ]
    norm_num
    linarith
  have htwo : (2:ℝ)≤2^(n+1) := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (by omega : 1≤n+1)
  calc
    _ ≤ 2*((CP*CV)^(n+1)*((n+1:ℕ):ℝ)^(5*order)*Real.exp (-κ*((n+1:ℕ):ℝ)^2)) :=
      mul_le_mul hscalar hreal' (norm_nonneg _) (by norm_num)
    _ ≤ 2^(n+1)*((CP*CV)^(n+1)*((n+1:ℕ):ℝ)^(5*order)*Real.exp (-κ*((n+1:ℕ):ℝ)^2)) :=
      mul_le_mul_of_nonneg_right htwo (by positivity)
    _ = _ := by simp only [mul_pow]; ring

end
end IsingBulk.HT.Contour
