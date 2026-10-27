import IsingBulk.Preferred22.AnchorScalarJets
import IsingBulk.Preferred22.PhysicalJacobianBound
import IsingBulk.Preferred22.SelectedOneBodyMajorant

/-! The unchanged regular-coordinate Jacobian on an anchored source is
dominated by the genuine independent angular profile, omitting its named
compact-left anchor. No derivative bound is assumed. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def preferredAnchorProfile {N : ℕ} (d : PreferredBranchData) (ε : ℝ)
    (a : Fin N) (θ : Fin N → ℝ) : ℝ :=
  ∏ i,if i=a then 1 else preferredSelectedOneBodyProfile d ε (θ i)

theorem preferredAnchorProfile_nonneg {N : ℕ} (d : PreferredBranchData) {ε : ℝ}
    (hε : 0<ε) (a : Fin N) (θ : Fin N → ℝ) : 0≤preferredAnchorProfile d ε a θ := by
  apply Finset.prod_nonneg
  intro i _
  split_ifs
  · norm_num
  · exact (preferred_selected_oneBody_profile_pos d hε _).le

theorem preferred_selected_profile_lower (d : PreferredBranchData) {ε : ℝ}
    (hε : 0<ε) (hε1 : ε≤1) (θ : ℝ) :
    1≤2*preferredSelectedOneBodyProfile d ε θ := by
  have hcos : |Real.cos d.b-Real.cos θ|≤2 := by
    exact (abs_sub _ _).trans (by linarith [Real.abs_cos_le_one d.b,Real.abs_cos_le_one θ])
  have harg : 0 < (|Real.cos d.b-Real.cos θ|+ε) := by positivity
  have hs : Real.sqrt (|Real.cos d.b-Real.cos θ|+ε)≤2 := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · norm_num
    · nlinarith
  change 1≤2*(Real.sqrt (|Real.cos d.b-Real.cos θ|+ε))⁻¹
  rw [←div_eq_mul_inv]
  exact (one_le_div (Real.sqrt_pos.mpr harg)).mpr hs

theorem preferred_physical_sine_inverse_norm {W : ℂ} (hW : 0<W.im) :
    ‖(Complex.sin (preferredArccos W))⁻¹‖=‖oneBody (physicalRoot W)‖ := by
  rw [←preferredArccos_physical_upper W hW,oneBody_exp_phase,mul_comm Complex.I,Complex.sinh_mul_I]
  simp only [norm_inv,norm_mul,Complex.norm_I,mul_one]

/-- A whole-contour one-coordinate Jacobian bound from the actual physical
one-body factor and the bounded imaginary shift. -/
theorem preferred_actual_inverse_Uq_profile (d : PreferredBranchData) (B : PreferredCoareaBump d) :
    ∃ C ε₀ τ₀ : ℝ,0<C ∧ 0<ε₀ ∧ 0<τ₀ ∧
      ∀ N : ℕ,0<N → ∀ ε τ : ℝ,0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
      ∀ θ : Fin N → ℝ,(∀ i,θ i∈Icc (-Real.pi-B.delta) B.delta) → ∀ i,
      ‖(preferredSourceUQ (IsingBulk.Branch.radialParameter d.alpha ε)
        (preferredSourceCoordinate τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ i))⁻¹‖≤
        C*preferredSelectedOneBodyProfile d ε (θ i) := by
  obtain ⟨A,ρ,hA,hρ,hρ1,hbody⟩ := preferred_actual_oneBody_profile d B
  obtain ⟨εf,hεf,hmargin⟩ := preferred_radial_one_sided_margins d B.delta B.delta_pos
    (by linarith [B.delta_alpha,d.alpha_pos])
  refine ⟨Real.exp 1*A+2,min ρ εf,min ρ 1,by positivity,lt_min hρ hεf,lt_min hρ zero_lt_one,?_⟩
  intro N hN ε τ hε hεr hτ hτr θ hθ i
  have heρ : ε<ρ := hεr.trans_le (min_le_left _ _)
  have htρ : τ<ρ := hτr.trans_le (min_le_left _ _)
  have ht1 : τ≤1 := (hτr.trans_le (min_le_right _ _)).le
  obtain ⟨hS,_hSi,hSδ⟩ := hmargin ε hε (hεr.trans_le (min_le_right _ _))
  have hsin : 0<Real.sin d.alpha := Real.sin_pos_of_pos_of_lt_pi d.alpha_pos
    (by linarith [d.alpha_lt,Real.pi_pos])
  have hW := (mul_pos hε hsin).trans_le (preferredActualW_im_lower d B hε.le hτ θ i)
  let w := deformedAngles τ B.p B.m θ i
  have hw : |w.im|≤1 := (preferred_deformedAngles_im_bound hN d B hτ θ i).trans ht1
  have hsw : ‖Complex.sin w‖≤Real.exp 1 := by
    rw [←Complex.cos_pi_div_two_sub]
    apply preferred_cos_norm_le_exp_one
    simpa only [Complex.sub_im,Complex.div_ofNat_im,Complex.ofReal_im,zero_div,zero_sub,abs_neg] using hw
  have hslope : ‖actualBumpSlopeVector d B ε τ θ i‖≤
      Real.exp 1*A*preferredSelectedOneBodyProfile d ε (θ i) := by
    change ‖preferredPhaseSlope (preferredRadialTrace d ε)
      (preferredBumpAngle B.m B.p τ (occupancy B.p θ/(N:ℝ)) (occupancy B.m θ/(N:ℝ)) (θ i))‖≤_
    rw [←actual_bump_angle]
    simp only [preferredPhaseSlope,div_eq_mul_inv,norm_mul,norm_neg,preferred_physical_sine_inverse_norm hW]
    exact (mul_le_mul hsw (hbody N hN ε τ hε heρ hτ htρ θ i) (norm_nonneg _) (Real.exp_pos 1).le).trans_eq (by ring)
  rw [preferred_inverse_Uq_on_source d B ε τ θ i hS hSδ (hθ i) hW]
  have hlower := preferred_selected_profile_lower d hε (heρ.le.trans hρ1) (θ i)
  calc
    _ ≤ ‖actualBumpSlopeVector d B ε τ θ i‖+1 := by simpa only [norm_one] using norm_add_le (actualBumpSlopeVector d B ε τ θ i) 1
    _ ≤ Real.exp 1*A*preferredSelectedOneBodyProfile d ε (θ i)+2*preferredSelectedOneBodyProfile d ε (θ i) := add_le_add hslope hlower
    _ = _ := by ring

/-- The named compact-left factor is uniformly bounded and is therefore
removed from the independent angular envelope. -/
theorem preferred_actual_anchor_Jacobian_profile (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d,B.delta<cap → ∀ δB : ℝ,0<δB →
      ∃ C ε₀ τ₀ : ℝ,0<C ∧ 0<ε₀ ∧ 0<τ₀ ∧
      ∀ N : ℕ,0<N → ∀ ε τ : ℝ,0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
      ∀ θ : Fin N → ℝ,(∀ i,θ i∈Icc (-Real.pi-B.delta) B.delta) →
      ∀ a : Fin N,θ a≤ -d.b-δB/2 →
      ‖preferredCoordinateJacobian τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ‖≤
        C^N*preferredAnchorProfile d ε a θ := by
  obtain ⟨cap,hcap,hcapa,hscalar⟩ := preferred_actual_anchor_scalar_jets d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hB δB hδB
  obtain ⟨εa,τa,_q₀,hεa,hτa,_hq₀,_hq₀1,hscalar'⟩ := hscalar B hB δB hδB
  obtain ⟨L,hL,hLjet⟩ := hscalar' 0
  obtain ⟨A,εp,τp,hA,hεp,hτp,hprofile⟩ := preferred_actual_inverse_Uq_profile d B
  obtain ⟨D,hD,hdet⟩ := preferred_contour_determinant_bound d B
  let K := max L A
  have hK : 0<K := lt_of_lt_of_le hA (le_max_right _ _)
  refine ⟨D*K,min εa εp,min τa (min τp 1),mul_pos hD hK,lt_min hεa hεp,
    lt_min hτa (lt_min hτp zero_lt_one),?_⟩
  intro N hN ε τ hε hεr hτ hτr θ hθ a ha
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  have hanchor : ‖(preferredSourceUQ s (preferredSourceCoordinate τ B.p B.m s θ a))⁻¹‖≤L := by
    have hh := ((hLjet N hN ε τ hε (hεr.trans_le (min_le_left _ _)) hτ
      (hτr.trans_le (min_le_left _ _)) θ hθ a).2.2.2.2 ha).1
    simpa only [norm_iteratedFDeriv_zero] using hh
  have hfactor (i : Fin N) :
      ‖(preferredSourceUQ s (preferredSourceCoordinate τ B.p B.m s θ i))⁻¹‖≤
        K*(if i=a then 1 else preferredSelectedOneBodyProfile d ε (θ i)) := by
    by_cases hi : i=a
    · subst i
      simpa only [ite_true,mul_one] using hanchor.trans (le_max_left L A)
    · rw [ite_eq_right hi]
      exact (hprofile N hN ε τ hε (hεr.trans_le (min_le_right _ _)) hτ
        (hτr.trans_le ((min_le_right _ _).trans (min_le_left _ _))) θ hθ i).trans
        (mul_le_mul_of_nonneg_right (le_max_right L A) (preferred_selected_oneBody_profile_pos d hε _).le)
  have hprod : (∏ i,‖(preferredSourceUQ s (preferredSourceCoordinate τ B.p B.m s θ i))⁻¹‖)≤
      K^N*preferredAnchorProfile d ε a θ := by
    calc
      _ ≤ ∏ i : Fin N,K*(if i=a then 1 else preferredSelectedOneBodyProfile d ε (θ i)) :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hfactor i)
      _ = _ := by simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,preferredAnchorProfile]
  simp only [preferredCoordinateJacobian,norm_mul,norm_prod]
  have hh := mul_le_mul (hdet N hN τ hτ (hτr.le.trans ((min_le_right _ _).trans (min_le_right _ _))) θ)
    hprod (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) (pow_nonneg hD.le N)
  exact hh.trans_eq (by rw [mul_pow]; ring)

end
end IsingBulk.Preferred22
