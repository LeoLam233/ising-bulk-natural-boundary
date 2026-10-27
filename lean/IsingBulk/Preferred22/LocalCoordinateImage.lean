import IsingBulk.Preferred22.CoordinateScale
import IsingBulk.Preferred22.CoordinateCenter

/-! Uniform scalar image control for the actual regular coordinate near
the physical branch, with every occupancy retained. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators Topology
open Set

set_option maxHeartbeats 900000 in
/-- The displaced physical branch-center coordinate is uniformly small for
all actual normalized occupancies, including positive outward displacement. -/
theorem preferred_displaced_center_coordinate_bound (d : PreferredBranchData)
    (B : PreferredCoareaBump d) :
    ∃ C ε₀ τ₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ 0 < τ₀ ∧
      ∀ ε τ σ υ : ℝ, 0 < ε → ε < ε₀ → 0 ≤ τ → τ < τ₀ →
      σ ∈ Icc 0 1 → υ ∈ Icc 0 1 →
      ‖preferredComparisonCoordinate d B ε τ σ υ 0‖ ≤ C*Real.sqrt (ε+τ) := by
  obtain ⟨_,Cs,rs,_,hCs,hrs,hs⟩ := preferred_outward_branch_control d
  obtain ⟨Cb,rb,hCb,hrb,hbranch⟩ := preferredMovingBranch_radial_bound d
  let ε₀ := min rs (min rb (1/2))
  let τ₀ := min rs (1/2)
  let A := Real.pi/2+1
  let C := A*Cs+Cb+1
  have hA : 0 < A := by dsimp [A]; positivity
  have hε₀ : 0 < ε₀ := lt_min hrs (lt_min hrb (by norm_num))
  have hτ₀ : 0 < τ₀ := lt_min hrs (by norm_num)
  refine ⟨C,ε₀,τ₀,by dsimp [C]; positivity,hε₀,hτ₀,?_⟩
  intro ε τ σ υ hε hεr hτ hτr hσ _hυ
  let δ := τ*σ
  have hδ : 0 ≤ δ := mul_nonneg hτ hσ.1
  have hδτ : δ ≤ τ := by dsimp [δ]; nlinarith [hσ.2]
  have hδr : δ < rs := hδτ.trans_lt (hτr.trans_le (min_le_left _ _))
  have hεrs : ε < rs := hεr.trans_le (min_le_left _ _)
  have hεrb : ε < rb := hεr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεhalf : ε < 1/2 := hεr.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hτhalf : τ < 1/2 := hτr.trans_le (min_le_right _ _)
  obtain ⟨_,hsine,_,_,_,hφlo,hφhi,_⟩ := hs ε δ 0 hε hεrs hδ hδr le_rfl hrs
  have hφ := preferred_phase_norm_le_sine (outwardPlateauPhase d ε δ 0) hφlo.le hφhi.le
  have hφbound : ‖outwardPlateauPhase d ε δ 0‖ ≤ A*Cs*Real.sqrt (ε+τ) := by
    have hh : ‖Complex.sin (outwardPlateauPhase d ε δ 0)‖ ≤ Cs*Real.sqrt (ε+δ) := by
      simpa only [zero_add] using hsine
    calc
      _ ≤ A*(Cs*Real.sqrt (ε+δ)) := hφ.trans (mul_le_mul_of_nonneg_left hh hA.le)
      _ ≤ A*(Cs*Real.sqrt (ε+τ)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) hCs.le) hA.le
      _ = _ := by ring
  have hB := hbranch ε hε.le hεrb
  have hwidth : |(0:ℝ)| < preferredBranchPlateauWidth d B := by
    simpa only [abs_zero] using preferredBranchPlateauWidth_pos d B
  have hqeq : preferredComparisonCoordinate d B ε τ σ υ 0 =
      outwardPlateauPhase d ε δ 0-
        (preferredMovingBranch (IsingBulk.Branch.radialParameter d.alpha ε)+(d.b:ℂ))-
        Complex.I*(δ:ℂ) := by
    dsimp only [preferredComparisonCoordinate]
    rw [preferred_actual_plateau_phase d B ε τ σ υ hwidth,
      preferred_actual_plateau_angle d B τ σ υ hwidth]
    unfold outwardPlateauAngle
    dsimp [δ]
    push_cast
    ring
  have hIδ : ‖Complex.I*(δ:ℂ)‖ = δ := by
    rw [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hδ]
  have hx : 0 < ε+τ := by positivity
  have hxsqrt : ε+τ ≤ Real.sqrt (ε+τ) := by
    nlinarith [Real.sq_sqrt hx.le,Real.sqrt_nonneg (ε+τ)]
  have htail : Cb*ε+δ ≤ (Cb+1)*Real.sqrt (ε+τ) := by
    have hh : Cb*ε+δ ≤ (Cb+1)*(ε+τ) := by nlinarith [mul_nonneg hCb.le hτ]
    exact hh.trans (mul_le_mul_of_nonneg_left hxsqrt (by positivity))
  rw [hqeq]
  have htri := norm_sub_le
    (outwardPlateauPhase d ε δ 0-(preferredMovingBranch (IsingBulk.Branch.radialParameter d.alpha ε)+(d.b:ℂ)))
    (Complex.I*(δ:ℂ))
  have htri2 := norm_sub_le (outwardPlateauPhase d ε δ 0)
    (preferredMovingBranch (IsingBulk.Branch.radialParameter d.alpha ε)+(d.b:ℂ))
  rw [hIδ] at htri
  dsimp [C]
  nlinarith only [htri,htri2,hφbound,hB,htail]

/-- Uniform integration from the actual fixed-occupancy comparison center.
This is a genuine endpoint estimate; no artificial analytic cutoff is used. -/
theorem preferred_comparison_coordinate_to_center (d : PreferredBranchData)
    (B : PreferredCoareaBump d) :
    ∃ C ε₀ τ₀ δB : ℝ, 0 < C ∧ 0 < ε₀ ∧ 0 < τ₀ ∧ 0 < δB ∧ δB < B.delta ∧
      ∀ ε τ σ υ u : ℝ, 0 < ε → ε < ε₀ → 0 ≤ τ → τ < τ₀ →
      σ ∈ Icc 0 1 → υ ∈ Icc 0 1 → -δB ≤ u → u ≤ d.b+B.delta →
      ‖preferredComparisonCoordinate d B ε τ σ υ u-preferredComparisonCoordinate d B ε τ σ υ 0‖ ≤
        C*Real.sqrt (|u|+ε) := by
  obtain ⟨C,ε₀,τ₀,δB,hC,hε₀,hτ₀,hδB,hδBδ,hbound⟩ :=
    preferred_fixed_occupancy_coordinate_difference d B
  refine ⟨C,ε₀,τ₀,δB,hC,hε₀,hτ₀,hδB,hδBδ,?_⟩
  intro ε τ σ υ u hε hεr hτ hτr hσ hυ huL huR
  let ρ := |u|+ε
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hd : ‖preferredComparisonCoordinate d B ε τ σ υ u-preferredComparisonCoordinate d B ε τ σ υ 0‖ ≤
      C*ρ/Real.sqrt (ρ+ε) := by
    by_cases hu : 0 ≤ u
    · have hh := hbound ε τ σ υ 0 u 0 ρ hε hεr hτ hτr hσ hυ (by linarith) hu huR hρ
        (by linarith) (by dsimp [ρ]; linarith [le_abs_self u])
      simpa only [abs_zero,zero_add] using hh
    · have hh := hbound ε τ σ υ u 0 0 ρ hε hεr hτ hτr hσ hυ huL (le_of_not_ge hu)
        (by linarith [d.b_pos,B.delta_pos]) hρ (by dsimp [ρ]; linarith [neg_abs_le u]) (by linarith)
      simpa only [abs_zero,zero_add,norm_sub_rev] using hh
  have hquot : ρ/Real.sqrt (ρ+ε) ≤ Real.sqrt ρ := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr (by positivity : 0 < ρ+ε))).mpr
    have hs := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith : ρ ≤ ρ+ε)) (Real.sqrt_nonneg ρ)
    nlinarith only [hs,Real.sq_sqrt hρ.le]
  calc
    _ ≤ C*ρ/Real.sqrt (ρ+ε) := hd
    _ = C*(ρ/Real.sqrt (ρ+ε)) := by ring
    _ ≤ C*Real.sqrt ρ := mul_le_mul_of_nonneg_left hquot hC.le

/-- Scalar image containment at the true branch, uniform in both occupancies.
For small |u|,epsilon,tau this places the actual q inside any fixed branch
coordinate neighborhood. -/
theorem preferred_comparison_coordinate_local_image (d : PreferredBranchData)
    (B : PreferredCoareaBump d) :
    ∃ C ε₀ τ₀ δB : ℝ, 0 < C ∧ 0 < ε₀ ∧ 0 < τ₀ ∧ 0 < δB ∧ δB < B.delta ∧
      ∀ ε τ σ υ u : ℝ, 0 < ε → ε < ε₀ → 0 ≤ τ → τ < τ₀ →
      σ ∈ Icc 0 1 → υ ∈ Icc 0 1 → -δB ≤ u → u ≤ d.b+B.delta →
      ‖preferredComparisonCoordinate d B ε τ σ υ u‖ ≤ C*Real.sqrt (|u|+ε+τ) := by
  obtain ⟨Cd,εd,τd,δB,hCd,hεd,hτd,hδB,hδBδ,hd⟩ := preferred_comparison_coordinate_to_center d B
  obtain ⟨Cc,εc,τc,hCc,hεc,hτc,hc⟩ := preferred_displaced_center_coordinate_bound d B
  refine ⟨Cd+Cc,min εd εc,min τd τc,δB,by positivity,lt_min hεd hεc,
    lt_min hτd hτc,hδB,hδBδ,?_⟩
  intro ε τ σ υ u hε hεr hτ hτr hσ hυ huL huR
  have hdiff := hd ε τ σ υ u hε (hεr.trans_le (min_le_left _ _)) hτ
    (hτr.trans_le (min_le_left _ _)) hσ hυ huL huR
  have hcenter := hc ε τ σ υ hε (hεr.trans_le (min_le_right _ _)) hτ
    (hτr.trans_le (min_le_right _ _)) hσ hυ
  have hd' := hdiff.trans (mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (by linarith : |u|+ε ≤ |u|+ε+τ)) hCd.le)
  have hc' := hcenter.trans (mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (by linarith [abs_nonneg u] : ε+τ ≤ |u|+ε+τ)) hCc.le)
  have htri := norm_add_le
    (preferredComparisonCoordinate d B ε τ σ υ u-preferredComparisonCoordinate d B ε τ σ υ 0)
    (preferredComparisonCoordinate d B ε τ σ υ 0)
  rw [sub_add_cancel] at htri
  nlinarith only [htri,hd',hc']

/-- The same local image bound for every literal actual source coordinate. -/
theorem preferred_actual_coordinate_local_image (d : PreferredBranchData)
    (B : PreferredCoareaBump d) :
    ∃ C ε₀ τ₀ δB : ℝ, 0 < C ∧ 0 < ε₀ ∧ 0 < τ₀ ∧ 0 < δB ∧ δB < B.delta ∧
      ∀ (N : ℕ), 0 < N → ∀ ε τ : ℝ, 0 < ε → ε < ε₀ → 0 ≤ τ → τ < τ₀ →
      ∀ θ : Fin N → ℝ, (∀ v, -δB ≤ θ v+d.b ∧ θ v+d.b ≤ d.b+B.delta) → ∀ i : Fin N,
      ‖preferredSourceCoordinate τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ i‖ ≤
        C*Real.sqrt (|θ i+d.b|+ε+τ) := by
  obtain ⟨C,ε₀,τ₀,δB,hC,hε₀,hτ₀,hδB,hδBδ,hbound⟩ := preferred_comparison_coordinate_local_image d B
  refine ⟨C,ε₀,τ₀,δB,hC,hε₀,hτ₀,hδB,hδBδ,?_⟩
  intro N hN ε τ hε hεr hτ hτr θ hbox i
  obtain ⟨hσ,hυ⟩ := actual_occupancy_box hN B θ
  have hh := hbound ε τ (occupancy B.p θ/(N:ℝ)) (occupancy B.m θ/(N:ℝ)) (θ i+d.b)
    hε hεr hτ hτr hσ hυ (hbox i).1 (hbox i).2
  rw [preferred_comparison_coordinate_actual] at hh
  exact hh

end
end IsingBulk.Preferred22
