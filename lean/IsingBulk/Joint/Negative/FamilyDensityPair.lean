import IsingBulk.Joint.Negative.FamilyDensityScalar
import IsingBulk.Anisotropic.NegativeNormalForm.DensityResiduePair

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Metric Filter IsingBulk.Anisotropic.NegativeNormalForm
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
set_option maxHeartbeats 1400000

theorem compact_family_negativePhase_near_center (B : ℂ × E → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {K : Set E} (hK : IsCompact K)
    (hB : ∀ eta ∈ K, AnalyticAt ℂ B (0,eta)) (ε : ℝ) (hε : 0<ε) :
    ∃ r : ℝ, 0<r ∧ ∀ eta ∈ K, ∀ p : ScalarTriple, ‖p‖<r →
      ‖negativePhase (familyMember B eta) phi hphi p.1 (p.2.1+p.2.2)-(phi:ℂ)*Complex.I‖<ε := by
  obtain ⟨r,L,M,hr,hL,_hM,_ha,hLip⟩ := compact_analytic_uniform_lipschitz
    (fun q : ScalarTriple × E => negativePhase (familyMember B q.2) phi hphi q.1.1 (q.1.2.1+q.1.2.2))
    hK (fun eta heta => family_negativePhase_moving_analyticAt B phi hphi eta (hB eta heta))
  refine ⟨min r (ε/(L+1)),lt_min hr (div_pos hε (by positivity)),?_⟩
  intro eta heta p hp
  have hh := hLip eta heta p 0 (hp.trans_le (min_le_left _ _)) (by simpa using hr)
  have hz : negativePhase (familyMember B eta) phi hphi 0 0=(phi:ℂ)*Complex.I := by
    simpa only [Complex.cos_zero,sub_self] using negativePhase_center (familyMember B eta) phi hphi 0
  simp only [Prod.fst_zero,Prod.snd_zero,zero_add,hz,sub_zero] at hh
  have hb := (lt_div_iff₀ (by positivity : 0<L+1)).mp (hp.trans_le (min_le_right _ _))
  exact hh.trans_lt (by nlinarith [norm_nonneg p])

theorem compact_family_residuePairRatio_control (B : ℂ × E → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {K : Set E} (hK : IsCompact K)
    (hB : ∀ eta ∈ K, AnalyticAt ℂ B (0,eta)) :
    ∃ r L : ℝ, 0<r ∧ 0<L ∧ ∀ eta ∈ K, ∀ t d x y : ℂ,
      ‖t‖<r → ‖1-Complex.cos d‖<r → ‖d‖<r → ‖x‖<r → ‖y‖<r →
      ‖residuePairRatio (familyMember B eta) phi hphi t d x y-1‖ ≤
        L*(‖t-(1-Complex.cos d)‖+‖d‖*(‖x‖+‖y‖)+‖x‖^2+‖y‖^2) := by
  obtain ⟨rp,P,hrp,hP,hphase⟩ := compact_family_negativePhase_moving_center_control B phi hphi hK hB
  obtain ⟨rs,M,hrs,hM,hsinh⟩ := sinh_pair_relative_control phi hphi
  obtain ⟨rh,H,hrh,hH,hhalf⟩ := halfSineSlope_relative_quadratic
  obtain ⟨rg,hrg,hgamma⟩ := compact_family_negativePhase_near_center B phi hphi hK hB rs hrs
  let r := min rp (min rg (rh/4))
  have hr : 0<r := lt_min hrp (lt_min hrg (by positivity))
  refine ⟨r,20*M*P+10*H,hr,by positivity,?_⟩
  intro eta heta t d x y ht ht₀ hd hx hy
  have hrp' : r≤rp := min_le_left _ _
  have hrg' : r≤rg := (min_le_right _ _).trans (min_le_left _ _)
  have hrh' : r≤rh/4 := (min_le_right _ _).trans (min_le_right _ _)
  have hpx := hphase eta heta t d x (ht.trans_le hrp') (ht₀.trans_le hrp') (hd.trans_le hrp') (hx.trans_le hrp')
  have hpy := hphase eta heta t d y (ht.trans_le hrp') (ht₀.trans_le hrp') (hd.trans_le hrp') (hy.trans_le hrp')
  have hgx := hgamma eta heta (t,(d,x)) ((max_lt ht (max_lt hd hx)).trans_le hrg')
  have hgy := hgamma eta heta (t,(d,y)) ((max_lt ht (max_lt hd hy)).trans_le hrg')
  obtain ⟨hbn,hbe⟩ := hsinh _ _ hgx hgy
  change ‖residuePairDenominatorRatio (familyMember B eta) phi hphi t d x y‖≤2 at hbn
  change ‖residuePairDenominatorRatio (familyMember B eta) phi hphi t d x y-1‖≤_ at hbe
  have hxy : ‖x-y‖<rh := by
    have hh := norm_sub_le x y
    have hx' := hx.trans_le hrh'
    have hy' := hy.trans_le hrh'
    linarith
  obtain ⟨han,hae⟩ := hhalf (x-y) hxy
  let E := ‖t-(1-Complex.cos d)‖+‖d‖*(‖x‖+‖y‖)+‖x‖^2+‖y‖^2
  have hE : 0≤E := by dsimp [E]; positivity
  have hsum : ‖negativePhase (familyMember B eta) phi hphi t (d+x)-(phi:ℂ)*Complex.I‖+
      ‖negativePhase (familyMember B eta) phi hphi t (d+y)-(phi:ℂ)*Complex.I‖≤2*P*E := by
    dsimp [E]
    nlinarith [mul_nonneg hP.le (norm_nonneg (t-(1-Complex.cos d))),
      mul_nonneg hP.le (mul_nonneg (norm_nonneg d) (add_nonneg (norm_nonneg x) (norm_nonneg y))),
      mul_nonneg hP.le (sq_nonneg ‖x‖),mul_nonneg hP.le (sq_nonneg ‖y‖)]
  have hbe' : ‖residuePairDenominatorRatio (familyMember B eta) phi hphi t d x y-1‖≤2*M*P*E := by
    have hh := hbe.trans (mul_le_mul_of_nonneg_left hsum hM.le)
    nlinarith
  have hxy2 : ‖x-y‖^2≤2*(‖x‖^2+‖y‖^2) := by
    have h := norm_sub_le x y
    nlinarith [sq_nonneg (‖x‖-‖y‖),norm_nonneg (x-y),norm_nonneg x,norm_nonneg y]
  have hae' : ‖2*halfSineSlope (x-y)-1‖≤2*H*E := by
    have hh := hae.trans (mul_le_mul_of_nonneg_left hxy2 hH.le)
    have he : ‖x‖^2+‖y‖^2≤E := by
      dsimp [E]
      nlinarith [norm_nonneg (t-(1-Complex.cos d)),mul_nonneg (norm_nonneg d) (add_nonneg (norm_nonneg x) (norm_nonneg y))]
    nlinarith [mul_le_mul_of_nonneg_left he hH.le]
  have hfinal := square_product_relative_error _ _ han hbn
  change ‖residuePairRatio (familyMember B eta) phi hphi t d x y-1‖≤_ at hfinal
  nlinarith


end
end IsingBulk.Joint.Negative
