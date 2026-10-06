import IsingBulk.Tail.MixedPairJets
import IsingBulk.Tail.MixedActiveResidualJets

/-! Branch-branch complete factors in the actual mixed source chart. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets Set Filter Metric
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false

theorem lower_halfplane_pair_gap {y w : ℂ} (hy : y.im<0) (hw : w.im<0) :
    1-y*w≠0 := by
  have hyn : y≠0 := by intro h; simp [h] at hy
  intro h
  have hp : y*w=1 := (sub_eq_zero.mp h).symm
  have he : w=y⁻¹ := by
    calc
      w=y⁻¹*(y*w) := by rw [← mul_assoc,inv_mul_cancel₀ hyn,one_mul]
      _=y⁻¹ := by rw [hp,mul_one]
  rw [he,Complex.inv_im] at hw
  have hn : 0<Complex.normSq y := Complex.normSq_pos.mpr hyn
  have hh : 0< -y.im/Complex.normSq y := div_pos (neg_pos.mpr hy) hn
  linarith

theorem mixed_actual_deformed_lower {N : ℕ} (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (θ : Fin N → ℝ) (i : Fin N) (hsin : Real.sin (θ i)<0) :
    (deformedPoint f r τ lam θ i).im<0 := by
  rw [deformedPoint_polar f hr τ lam θ i,Complex.exp_im]
  simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,Complex.I_im,
    Complex.I_re,mul_one,mul_zero,add_zero,zero_add]
  exact mul_neg_of_pos_of_neg (Real.exp_pos _) hsin

theorem mixed_actual_branch_pair_identification {N : ℕ} (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (i j : Fin N)
    (hsi : Real.sin (θ i)<0) (hsj : Real.sin (θ j)<0)
    (hWi : 0<(sourceW s (deformedPoint f r τ lam θ i)).im)
    (hWj : 0<(sourceW s (deformedPoint f r τ lam θ j)).im) :
    branchCompletePair (s,mixedContourPhase f r τ lam s θ i,mixedContourPhase f r τ lam s θ j)=
      canceledPair (deformedPoint f r τ lam θ i) (deformedPoint f r τ lam θ j)
        (globalRoot s (deformedPoint f r τ lam θ i)) (globalRoot s (deformedPoint f r τ lam θ j)) := by
  let p := mixedContourPhase f r τ lam s θ i
  let q := mixedContourPhase f r τ lam s θ j
  have hyden := lower_halfplane_pair_gap (mixed_actual_deformed_lower f hr τ lam θ i hsi)
    (mixed_actual_deformed_lower f hr τ lam θ j hsj)
  have hregi : regularY s p=deformedPoint f r τ lam θ i := mixed_actual_regularY f hr τ lam s θ i hsi
  have hregj : regularY s q=deformedPoint f r τ lam θ j := mixed_actual_regularY f hr τ lam s θ j hsj
  have hzi : globalRoot s (deformedPoint f r τ lam θ i)=Complex.exp (-Complex.I*p) := globalRoot_eq_exp_lowerArccos _ _
  have hzj : globalRoot s (deformedPoint f r τ lam θ j)=Complex.exp (-Complex.I*q) := globalRoot_eq_exp_lowerArccos _ _
  have hzden : 1-Complex.exp (-Complex.I*p)*Complex.exp (-Complex.I*q)≠0 := by
    rw [← hzi,← hzj]
    exact one_sub_mul_ne_zero_of_norm_lt_one (interiorRoot_norm_lt_one hWi) (interiorRoot_norm_lt_one hWj)
  have hd : 1-(regularY s p*regularY s q)⁻¹≠0 := by
    rw [hregi,hregj]
    intro he
    have hx := inv_eq_one.mp (sub_eq_zero.mp he).symm
    exact hyden (by rw [hx]; simp)
  have he : 1-Complex.exp (-Complex.I*p)*Complex.exp (-Complex.I*q)=
      (p+q)*exponentialQuotient (p+q) := by
    rw [mul_exponentialQuotient,← Complex.exp_add]
    congr 2
    ring
  have hsum : p+q≠0 := by intro h; apply hzden; rw [he,h,zero_mul]
  have hJ : exponentialQuotient (p+q)≠0 := by intro h; apply hzden; rw [he,h,mul_zero]
  have hh := branchCompletePair_eq_rational s p q hd hsum hJ
  rw [hregi,hregj] at hh
  rw [hzi,hzj]
  exact hh

theorem mixed_actual_branch_branch_pair_jets (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) (cap : ℝ) (hcap : 0<cap) (order : ℕ) :
    ∃ inner₀ c e t₀ C : ℝ,0< inner₀ ∧ inner₀≤cap ∧ 0<c ∧ 0<e ∧ 0<t₀ ∧ 0<C ∧
      ∀ η α : ℝ,0<η → η≤Real.sin d.thetaB/4 → 0<α →
      ∀ (N : ℕ) (eps τ lam : ℝ) (θ : Fin N → ℝ) (i j : Fin N) (s : ℂ),
      1≤N → 0<eps → eps<e → 0≤τ → 0≤lam → lam≤1 → lam*τ<t₀ →
      |sectorDisplacement d.thetaB (θ i)|≤ inner₀ →
      |sectorDisplacement d.thetaB (θ j)|≤ inner₀ →
      ‖s-radialParameter d.theta eps‖≤c*eps →
      let y := deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ lam θ
      let p := (s,mixedSourcePhase s (y i),mixedSourcePhase s (y j))
      AnalyticAt ℂ branchCompletePair p ∧ ∀ l≤order,‖iteratedFDeriv ℂ l branchCompletePair p‖≤C := by
  let s₀ := radialParameter d.theta 0
  have hs : s₀≠0 := norm_ne_zero_iff.mp (by
    change ‖radialParameter d.theta 0‖≠0
    rw [radialParameter_norm (by norm_num)]
    norm_num)
  have hS : s₀+s₀⁻¹=(1+(Real.cos d.thetaB:ℂ)) := by
    simpa [s₀,IsingBulk.First.sourceS] using sourceS_radial_zero_branch d
  have hc : |Real.cos d.thetaB|<1 := by
    have hsin : 0<Real.sin d.thetaB := d.a_pos
    rw [abs_lt]
    constructor <;> nlinarith [hsin,Real.sin_sq_add_cos_sq d.thetaB,
      Real.cos_le_one d.thetaB,Real.neg_one_le_cos d.thetaB]
  have ha := branchCompletePair_analytic s₀ (Real.cos d.thetaB) hs hS hc
  obtain ⟨C,hC,hjets⟩ := finite_analytic_jets_bounded _ _ ha order
  have hanear : ∀ᶠ p in 𝓝 (s₀,(0:ℂ),(0:ℂ)),AnalyticAt ℂ branchCompletePair p :=
    (isOpen_analyticAt ℂ branchCompletePair).mem_nhds ha
  have hnear := hanear.and hjets
  obtain ⟨δ,hδ,hball⟩ := Metric.eventually_nhds_iff.mp hnear
  let U : Set (ℂ × ℂ) := ball (s₀,0) (δ/2)
  have hbase : (s₀,(0:ℂ))∈U := mem_ball_self (by positivity)
  obtain ⟨inner₀,c,e,t₀,hi,hicap,hc,he,ht,hBranch⟩ :=
    mixed_actual_branch_chart_neighborhood d hcsmall U isOpen_ball hbase cap hcap
  refine ⟨inner₀,c,e,t₀,C,hi,hicap,hc,he,ht,hC,?_⟩
  intro η α hη hηsmall hα N eps τ lam θ i j s hN heps hepslt hτ hl0 hl1 htl hpi hpj hsd
  have hBi := hBranch η α hη hηsmall hα N eps τ lam θ i s hN heps hepslt hτ hl0 hl1 htl hpi hsd
  have hBj := hBranch η α hη hηsmall hα N eps τ lam θ j s hN heps hepslt hτ hl0 hl1 htl hpj hsd
  apply hball
  have hi' := max_lt_iff.mp (show max (dist s s₀)
    (dist (mixedSourcePhase s (deformedPoint (constructedSelector d.thetaB η α)
      (Real.exp (-d.c₀*eps)) τ lam θ i)) 0)<δ/2 by simpa only [U,mem_ball,Prod.dist_eq] using hBi)
  have hj' := max_lt_iff.mp (show max (dist s s₀)
    (dist (mixedSourcePhase s (deformedPoint (constructedSelector d.thetaB η α)
      (Real.exp (-d.c₀*eps)) τ lam θ j)) 0)<δ/2 by simpa only [U,mem_ball,Prod.dist_eq] using hBj)
  rw [Prod.dist_eq,Prod.dist_eq]
  exact max_lt (hi'.1.trans (half_lt_self hδ))
    (max_lt (hi'.2.trans (half_lt_self hδ)) (hj'.2.trans (half_lt_self hδ)))

def mixedActiveBranchPairCoordinate {N : ℕ} (i j : Fin N) : MixedActiveSpace N →L[ℂ] (ℂ × ℂ × ℂ) :=
  (ContinuousLinearMap.fst ℂ ℂ ((Fin N → ℂ) × ℂ)).prod
    (((ContinuousLinearMap.proj (R := ℂ) i).comp
      ((ContinuousLinearMap.fst ℂ (Fin N → ℂ) ℂ).comp
        (ContinuousLinearMap.snd ℂ ℂ ((Fin N → ℂ) × ℂ)))).prod
     ((ContinuousLinearMap.proj (R := ℂ) j).comp
      ((ContinuousLinearMap.fst ℂ (Fin N → ℂ) ℂ).comp
        (ContinuousLinearMap.snd ℂ ℂ ((Fin N → ℂ) × ℂ)))))

theorem mixedActiveBranchPairCoordinate_norm {N : ℕ} (i j : Fin N) :
    ‖mixedActiveBranchPairCoordinate i j‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  change ‖(u.1,u.2.1 i,u.2.1 j)‖≤1*‖u‖
  simp only [one_mul,Prod.norm_def]
  refine max_le (le_max_left _ _) (max_le ?_ ?_)
  · exact (norm_le_pi_norm u.2.1 i).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (norm_le_pi_norm u.2.1 j).trans ((le_max_left _ _).trans (le_max_right _ _))

def mixedActiveBranchPair {N : ℕ} (s : ℂ) (φ : Fin N → ℂ) (i j : Fin N)
    (u : MixedActiveSpace N) : ℂ := branchCompletePair (s+u.1,φ i+u.2.1 i,φ j+u.2.1 j)

theorem mixedActiveBranchPair_jet_bound {N : ℕ} (s : ℂ) (φ : Fin N → ℂ) (i j : Fin N) (k : ℕ)
    (hF : AnalyticAt ℂ branchCompletePair (s,φ i,φ j)) :
    AnalyticAt ℂ (mixedActiveBranchPair s φ i j) 0 ∧
    ‖iteratedFDeriv ℂ k (mixedActiveBranchPair s φ i j) 0‖≤
      ‖iteratedFDeriv ℂ k branchCompletePair (s,φ i,φ j)‖ := by
  have he : mixedActiveBranchPair s φ i j=(fun u => branchCompletePair
      (mixedActiveBranchPairCoordinate i j u+(s,φ i,φ j))) := by
    funext u
    simp [mixedActiveBranchPair,mixedActiveBranchPairCoordinate,add_comm]
  have hF' : AnalyticAt ℂ branchCompletePair (mixedActiveBranchPairCoordinate i j 0+(s,φ i,φ j)) := by
    simpa using hF
  rw [he]
  refine ⟨hF'.comp (f := fun u => mixedActiveBranchPairCoordinate i j u+(s,φ i,φ j))
    (((mixedActiveBranchPairCoordinate i j).analyticAt 0).add analyticAt_const),?_⟩
  simpa using analytic_affine_pullback_jet_norm (mixedActiveBranchPairCoordinate i j)
    branchCompletePair (s,φ i,φ j) 0 hF' (mixedActiveBranchPairCoordinate_norm i j) k

theorem canceledPair_swap (yi yj zi zj : ℂ) : canceledPair yi yj zi zj=canceledPair yj yi zj zi := by
  unfold canceledPair
  congr 1 <;> ring

theorem mixed_actual_branch_compact_pair_identification {N : ℕ} (f : SelectorFunctions)
    {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (i j : Fin N)
    (hsi : Real.sin (θ i)<0) (hWj : 0<(sourceW s (deformedPoint f r τ lam θ j)).im) :
    mixedBranchCompactPair (s,mixedContourPhase f r τ lam s θ i,deformedPoint f r τ lam θ j)=
      canceledPair (deformedPoint f r τ lam θ i) (deformedPoint f r τ lam θ j)
        (globalRoot s (deformedPoint f r τ lam θ i)) (globalRoot s (deformedPoint f r τ lam θ j)) := by
  unfold mixedBranchCompactPair
  rw [mixed_actual_regularY f hr τ lam s θ i hsi]
  have hzi : globalRoot s (deformedPoint f r τ lam θ i)=
      Complex.exp (-Complex.I*mixedContourPhase f r τ lam s θ i) := globalRoot_eq_exp_lowerArccos _ _
  rw [← hzi,selectedContinuedRoot,continuedRoot_eq_interiorRoot hWj]
  rfl

end
end IsingBulk.Tail
