import IsingBulk.Preferred22.RightDomain
import IsingBulk.Preferred22.RegularTransport
import IsingBulk.Preferred22.ContourHomotopyJets
import IsingBulk.Preferred22.MarkedMinorNormalization
import IsingBulk.Preferred22.JacobianContinuity
import IsingBulk.Preferred22.CoordinateScale

/-! Actual j=0 q20 domination, retaining the literal physical seed,
normalization, contour Jacobian and product resolvent. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set MeasureTheory
open scoped BigOperators Topology ContDiff

theorem PreferredCoareaBump.m_periodic {d : PreferredBranchData} (B : PreferredCoareaBump d) :
    Function.Periodic B.m (2*Real.pi) := by
  intro x
  change B.p (-(x+2*Real.pi))=B.p (-x)
  convert (B.periodic (-x-2*Real.pi)).symm using 1 <;> congr 1 <;> ring

theorem preferredContourMatrix_eq_full {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ) (θ : Fin N → ℝ) :
    preferredContourMatrix τ p m θ=fullAngularJacobian 1 τ p m θ := by
  ext i j
  unfold preferredContourMatrix fullAngularJacobian shiftJacobian
  push_cast
  ring

/-- One exponential contour-Jacobian bound works before N and every small
actual deformation amplitude. It follows from the proved full homotopy jets. -/
theorem preferred_contour_determinant_bound (d : PreferredBranchData) (B : PreferredCoareaBump d) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ), 0<N → ∀ (τ : ℝ), 0≤τ → τ≤1 →
      ∀ θ : Fin N → ℝ, ‖(preferredContourMatrix τ B.p B.m θ).det‖≤C^N := by
  obtain ⟨C,hC,hb⟩ := fullAngularJacobian_homotopy_uniform_jets B.p B.m B.smooth B.m_smooth
    B.periodic B.m_periodic 1 0
  refine ⟨C,hC,?_⟩
  intro N hN τ hτ hτ1 θ
  rw [preferredContourMatrix_eq_full]
  have hh := hb τ (by simpa only [abs_of_nonneg hτ] using hτ1) N hN θ 0 le_rfl
  simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one] using hh

theorem preferred_right_weight_bounds {N : ℕ} (η p m r : ℝ → ℝ)
    (hη : ∀ x,η x∈Icc 0 1) (hr : ∀ x,r x∈Icc 0 1) (θ : Fin N → ℝ) :
    preferredCellWeight .right η p m r θ∈Icc 0 1 := by
  have ha := hη (occupancy p θ)
  have hb := hη (occupancy m θ)
  obtain ⟨hf,hl,hu⟩ := partition_nonnegative ha.1 ha.2 hb.1 hb.2
  have hl1 : lowerWeight (η (occupancy p θ)) (η (occupancy m θ))≤1 := by
    linarith [full_partition (η (occupancy p θ)) (η (occupancy m θ))]
  have hp0 : 0≤∏ i,r (θ i) := Finset.prod_nonneg (fun i _ => (hr (θ i)).1)
  have hp1 : (∏ i,r (θ i))≤1 :=
    Finset.prod_le_one₀ (fun i _ => (hr (θ i)).1) (fun i _ => (hr (θ i)).2)
  exact ⟨mul_nonneg hl hp0,by
    simpa only [one_mul,preferredCellWeight,preferredLowerWeight,preferredRightWeight] using mul_le_mul hl1 hp1 hp0 (by norm_num : (0:ℝ)≤1)⟩

theorem preferredActualZ_norm_le_one {N : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {ε τ : ℝ} (hε : 0<ε) (hτ : 0≤τ) (θ : Fin N → ℝ) :
    ‖preferredActualZ d B ε τ θ‖≤1 := by
  have hs : 0<Real.sin d.alpha := Real.sin_pos_of_pos_of_lt_pi d.alpha_pos
    (by linarith [d.alpha_lt,Real.pi_pos])
  unfold preferredActualZ
  rw [norm_prod]
  apply Finset.prod_le_one₀ (fun i _ => norm_nonneg _)
  intro i _
  have hW := (mul_pos hε hs).trans_le (preferredActualW_im_lower d B hε.le hτ θ i)
  exact (physicalRoot_inside (Or.inl hW.ne')).le

/-- The untransported regular-coordinate Jacobian has exactly the retained
physical one-body derivative factors, with no inverse-Uq bound assumed. -/
theorem preferred_inverse_Uq_on_source {N : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (ε τ : ℝ) (θ : Fin N → ℝ) (i : Fin N)
    (hS : 0<(preferredRadialTrace d ε).re)
    (hSδ : (preferredRadialTrace d ε).re<2*Real.cos B.delta)
    (hθ : θ i∈Icc (-Real.pi-B.delta) B.delta)
    (hW : 0<(preferredRadialTrace d ε-Complex.cos (deformedAngles τ B.p B.m θ i)).im) :
    (preferredSourceUQ (IsingBulk.Branch.radialParameter d.alpha ε)
      (preferredSourceCoordinate τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ i))⁻¹ =
        actualBumpSlopeVector d B ε τ θ i+1 := by
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  let w := deformedAngles τ B.p B.m θ i
  have hre : w.re=θ i := by dsimp [w,deformedAngles]; simp
  have hδπ : B.delta<Real.pi/2 := by linarith [B.delta_alpha,d.alpha_lt,Real.pi_pos]
  have hf := preferred_forward_coordinate_hasDerivAt s w B.delta B.delta_pos hδπ hS hSδ
    (by rw [hre]; exact hθ.1) (by rw [hre]; exact hθ.2) hW
  have hg := ((preferredAngularPhase_hasDerivAt d ε hW).add (hasDerivAt_id w)).sub_const (preferredMovingBranch s)
  have hh := hf.unique hg
  change (preferredSourceUQ s (preferredSourceCoordinate τ B.p B.m s θ i))⁻¹=
    preferredPhaseSlope (preferredRadialTrace d ε) (deformedAngles τ B.p B.m θ i)+1 at hh
  rw [actual_bump_angle] at hh
  exact hh

/-- The literal regular product phase is the complete physical product on
an actual source contour with the derived global moving inverse. -/
theorem preferred_regular_product_on_source {N : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {ε τ : ℝ} (hε : 0<ε) (hτ : 0≤τ) (θ : Fin N → ℝ)
    (hU : ∀ i,preferredMovingInverse (IsingBulk.Branch.radialParameter d.alpha ε)
      (preferredSourceCoordinate τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ i)=
        deformedAngles τ B.p B.m θ i) :
    preferredRegularProductPhase (IsingBulk.Branch.radialParameter d.alpha ε)
      (preferredSourceCoordinate τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ)=
        preferredActualZ d B ε τ θ := by
  rw [preferredActualZ_eq_exp d B hε hτ]
  unfold preferredRegularProductPhase
  simp_rw [preferred_regular_phase_on_source τ B.p B.m _ θ hU]
  rfl

/-- Actual normalized determinant size, with no marked-minor size premise. -/
theorem preferred_regular_determinant_normalized {N : ℕ} (hN : 0<N)
    (s : ℂ) (q : Fin N → ℂ) {a : ℝ} (ha : 0<a)
    (hK : ∀ i j,‖preferredRegularKernel s q i j‖≤a) :
    ‖(preferredRegularKernel s q).det‖/(N.factorial:ℝ) ≤
      (Real.exp 1/Real.sqrt N)^N*a^N := by
  have hh := markedDeterminant_factorial_bound (ell := 0) hN (preferredRegularKernel s q)
    (Fin.elim0) a ha hK
  simpa only [markedDeterminant,iteratedFDeriv_zero_apply,Nat.sub_zero] using hh


/-- Actual physical j=0 pointwise q20 estimate from actual matrix-entry and
one-body size bounds. The determinant size is derived by the proved Gram
bound and exact factorial normalization. -/
theorem preferred_zeroth_pointwise_majorant {N : ℕ} (hN : 0<N)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {ε τ : ℝ}
    (hε : 0<ε) (hτ : 0≤τ) (θ : Fin N → ℝ) (η rcut : ℝ → ℝ)
    (hη : ∀ x,η x∈Icc 0 1) (hrcut : ∀ x,rcut x∈Icc 0 1)
    (hS : 0<(preferredRadialTrace d ε).re)
    (hSδ : (preferredRadialTrace d ε).re<2*Real.cos B.delta)
    (hθ : ∀ i,θ i∈Icc (-Real.pi-B.delta) B.delta)
    {M A a : ℝ} (hM0 : 0<M) (_hA0 : 0<A) (ha0 : 0<a)
    (hM : ‖(preferredContourMatrix τ B.p B.m θ).det‖≤M^N)
    (hA : ∀ i,‖preferredRegularOneBody (IsingBulk.Branch.radialParameter d.alpha ε)
      (preferredSourceCoordinate τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ i)‖≤A)
    (hK : ∀ i j,‖preferredRegularKernel (IsingBulk.Branch.radialParameter d.alpha ε)
      (preferredSourceCoordinate τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ) i j‖≤a) :
    ‖preferredTransportedDensity .right τ η B.p B.m rcut 0
      (IsingBulk.Branch.radialParameter d.alpha ε) θ‖ ≤
      2*(M*A)^N*(Real.exp 1/Real.sqrt N)^N*a^N*preferredJacobianResolvent d B ε τ θ := by
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  let q := preferredSourceCoordinate τ B.p B.m s θ
  have hδπ : B.delta<Real.pi/2 := by linarith [B.delta_alpha,d.alpha_lt,Real.pi_pos]
  have hs : 0<Real.sin d.alpha := Real.sin_pos_of_pos_of_lt_pi d.alpha_pos
    (by linarith [d.alpha_lt,Real.pi_pos])
  have hW (i : Fin N) : 0<(preferredRadialTrace d ε-Complex.cos (deformedAngles τ B.p B.m θ i)).im :=
    (mul_pos hε hs).trans_le (preferredActualW_im_lower d B hε.le hτ θ i)
  have hU (i : Fin N) : preferredMovingInverse s (q i)=deformedAngles τ B.p B.m θ i := by
    have hre : (deformedAngles τ B.p B.m θ i).re=θ i := by simp [deformedAngles]
    exact preferred_global_one_sided_inverse s (deformedAngles τ B.p B.m θ i) B.delta
      B.delta_pos hδπ hS hSδ (by rw [hre]; exact (hθ i).1) (by rw [hre]; exact (hθ i).2) (hW i)
  have hseed := preferred_one_sided_seed_eq_regular (.right : PreferredTransportCell N)
    τ B.delta η B.p B.m rcut s θ B.delta_pos hδπ hS hSδ hθ hW
  have hZ := preferred_regular_product_on_source d B hε hτ θ hU
  have hinv (i : Fin N) : (preferredSourceUQ s (q i))⁻¹=actualBumpSlopeVector d B ε τ θ i+1 :=
    preferred_inverse_Uq_on_source d B ε τ θ i hS hSδ (hθ i) (hW i)
  have hw := preferred_right_weight_bounds η B.p B.m rcut hη hrcut θ
  have hwn : |preferredCellWeight .right η B.p B.m rcut θ|≤1 := by
    rw [abs_of_nonneg hw.1]
    exact hw.2
  have hnum : ‖1+preferredActualZ d B ε τ θ‖≤2 := by
    calc
      _ ≤ ‖(1:ℂ)‖+‖preferredActualZ d B ε τ θ‖ := norm_add_le _ _
      _ ≤ 2 := by rw [norm_one]; linarith [preferredActualZ_norm_le_one d B hε hτ θ]
  have hdet := preferred_regular_determinant_normalized hN s q ha0 hK
  have hprod : (∏ i,‖preferredRegularOneBody s (q i)‖)≤A^N := by
    have hh := Finset.prod_le_prod₀ (fun i (_ : i∈Finset.univ) => norm_nonneg (preferredRegularOneBody s (q i)))
      (fun i _ => hA i)
    simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using hh
  have hHaar : 1≤(2*Real.pi)^(N-1) := one_le_pow₀ (by linarith [Real.two_le_pi])
  have hformula : ‖preferredTransportedDensity .right τ η B.p B.m rcut 0 s θ‖ =
      (|preferredCellWeight .right η B.p B.m rcut θ| *‖(preferredContourMatrix τ B.p B.m θ).det‖*
        ‖1+preferredActualZ d B ε τ θ‖*(‖(preferredRegularKernel s q).det‖/(N.factorial:ℝ))*
        (∏ i,‖preferredRegularOneBody s (q i)‖)/(2*Real.pi)^(N-1))*
        preferredJacobianResolvent d B ε τ θ := by
    rw [preferredTransportedDensity_zero,hseed]
    simp only [preferredCoordinateJacobian,preferredRegularAmplitude,norm_mul,norm_div,norm_prod,norm_pow,
      Complex.norm_natCast,Complex.norm_real,Real.norm_eq_abs,Complex.norm_ofNat,abs_of_pos Real.pi_pos]
    dsimp only [q] at hinv
    simp_rw [hinv]
    rw [hZ]
    unfold preferredJacobianResolvent
    ring
  have h01 := mul_le_mul hwn hM (norm_nonneg _) (by norm_num : (0:ℝ)≤1)
  have h02 := mul_le_mul h01 hnum (norm_nonneg _) (by positivity)
  have h03 := mul_le_mul h02 hdet (by positivity) (by positivity)
  have h04 := mul_le_mul h03 hprod (Finset.prod_nonneg (fun i _ => norm_nonneg _)) (by positivity)
  have hquot := (div_le_self (by positivity : 0≤
      |preferredCellWeight .right η B.p B.m rcut θ| *‖(preferredContourMatrix τ B.p B.m θ).det‖*
        ‖1+preferredActualZ d B ε τ θ‖*(‖(preferredRegularKernel s q).det‖/(N.factorial:ℝ))*
        (∏ i,‖preferredRegularOneBody s (q i)‖)) hHaar).trans h04
  rw [hformula]
  calc
    _ ≤ (1*M^N*2*((Real.exp 1/Real.sqrt N)^N*a^N)*A^N)*preferredJacobianResolvent d B ε τ θ :=
      mul_le_mul_of_nonneg_right hquot (preferredJacobianResolvent_nonneg d B ε τ θ)
    _ = _ := by rw [mul_pow]; ring


/-- Unconditional j=0 q20 on the actual full right contour. The source cap
is chosen before the smooth bumps, as in the manuscript. All entry, one-body,
Jacobian, phase and factorial bounds are established in the proof. -/
theorem preferred_zeroth_source_majorant (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧ ∀ B : PreferredCoareaBump d,B.delta<cap →
      ∃ C ε₀ τ₀ δ₀ : ℝ,0<C ∧ 0<ε₀ ∧ 0<τ₀ ∧ 0<δ₀ ∧ δ₀<B.delta ∧
      ∀ N : ℕ,2≤N → ∀ ε τ t r : ℝ,0<ε → ε<ε₀ → 0≤τ → τ<τ₀ → 0<r →
      ∀ θ : Fin N → ℝ,
      (∀ v,-δ₀≤θ v+d.b ∧ θ v+d.b≤d.b+B.delta) →
      (∀ v,t-2*r≤θ v+d.b ∧ θ v+d.b≤t+2*r) →
      ∀ η rcut : ℝ → ℝ,(∀ x,η x∈Icc 0 1) → (∀ x,rcut x∈Icc 0 1) →
      ‖preferredTransportedDensity .right τ η B.p B.m rcut 0
        (IsingBulk.Branch.radialParameter d.alpha ε) θ‖ ≤
        2*(C/Real.sqrt N)^N*(r/Real.sqrt (|t|+r+ε))^N*preferredJacobianResolvent d B ε τ θ := by
  obtain ⟨cap,hcap,hcapa,hsize⟩ := preferred_actual_regular_size d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hBcap
  obtain ⟨τs,δs,εs,Cs,hτs,hδs,hεs,hCs,hs⟩ := hsize B.delta B.delta_pos hBcap B.p B.m
    B.smooth.continuous B.m_smooth.continuous
    (fun x => ⟨B.lower_bound x,B.upper_bound x⟩)
    (fun x => ⟨B.lower_bound (-x),B.upper_bound (-x)⟩)
    (fun x hx => B.p_zero_of_sin_nonpos hx) (fun x hx => B.m_zero_of_sin_nonneg hx)
  obtain ⟨Cd,εd,τd,δd,hCd,hεd,hτd,hδd,hδdδ,hd⟩ := preferred_actual_coordinate_difference d B
  obtain ⟨CM,hCM,hM⟩ := preferred_contour_determinant_bound d B
  obtain ⟨εm,hεm,hm⟩ := preferred_radial_one_sided_margins d B.delta B.delta_pos (by linarith [B.delta_alpha,d.alpha_pos])
  let C := CM*Cs^2*Cd*Real.exp 1
  let ε₀ := min εs (min εd εm)
  let τ₀ := min τs (min τd 1)
  let δ₀ := min δs δd
  have hC : 0<C := by dsimp [C]; positivity
  have hε₀ : 0<ε₀ := lt_min hεs (lt_min hεd hεm)
  have hτ₀ : 0<τ₀ := lt_min hτs (lt_min hτd (by norm_num))
  have hδ₀ : 0<δ₀ := lt_min hδs hδd
  have hδ₀δ : δ₀<B.delta := (min_le_right _ _).trans_lt hδdδ
  refine ⟨C,ε₀,τ₀,δ₀,hC,hε₀,hτ₀,hδ₀,hδ₀δ,?_⟩
  intro N hN ε τ t r hε hεr hτ hτr hr θ hbox hwindow η rcut hη hrcut
  have hN0 : 0<N := by omega
  have hεs' : ε<εs := hεr.trans_le (min_le_left _ _)
  have hεd' : ε<εd := hεr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεm' : ε<εm := hεr.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hτs' : τ<τs := hτr.trans_le (min_le_left _ _)
  have hτd' : τ<τd := hτr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hτ1 : τ≤1 := (hτr.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
  have hboxs : θ∈preferredRightAngularBox d B.delta δs N := by
    intro v
    have hv := hbox v
    constructor
    · have hh : δ₀≤δs := min_le_left _ _
      linarith [hv.1]
    · linarith [hv.2]
  have hboxd (v : Fin N) : -δd≤θ v+d.b ∧ θ v+d.b≤d.b+B.delta :=
    ⟨(neg_le_neg (min_le_right _ _)).trans (hbox v).1,(hbox v).2⟩
  have hθ (v : Fin N) : θ v∈Icc (-Real.pi-B.delta) B.delta := by
    have hv := hbox v
    constructor <;> linarith [hv.1,hv.2,hδ₀δ,d.b_lt]
  have hreg := hs τ hτ hτs' N hN ε θ hε hεs' hboxs
  obtain ⟨hSr,_hSi,hSδ⟩ := hm ε hε hεm'
  have hdiff := hd N hN0 ε τ t r hε hεd' hτ hτd' hr θ hboxd hwindow
  have hT : 0<Real.sqrt (|t|+r+ε) := Real.sqrt_pos.2 (by positivity)
  have ha : 0<Cs*Cd*r/Real.sqrt (|t|+r+ε) := by positivity
  have hK (i j : Fin N) : ‖preferredRegularKernel (IsingBulk.Branch.radialParameter d.alpha ε)
      (preferredSourceCoordinate τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ) i j‖≤
      Cs*Cd*r/Real.sqrt (|t|+r+ε) := by
    calc
      _ ≤ Cs*‖preferredSourceCoordinate τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ i-
          preferredSourceCoordinate τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ j‖ := (hreg i).2 j
      _ ≤ Cs*(Cd*r/Real.sqrt (|t|+r+ε)) := mul_le_mul_of_nonneg_left (hdiff i j) hCs.le
      _ = _ := by ring
  have hb := preferred_zeroth_pointwise_majorant hN0 d B hε hτ θ η rcut hη hrcut hSr hSδ hθ
    hCM hCs ha (hM N hN0 τ hτ hτ1 θ) (fun i => (hreg i).1) hK
  calc
    _ ≤ _ := hb
    _ = _ := by dsimp [C]; simp only [mul_pow,div_pow]; ring

end
end IsingBulk.Preferred22
