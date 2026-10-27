import IsingBulk.Preferred22.CoordinateScale
import IsingBulk.Preferred22.CoordinateCenter

/-! The complete absolute q-coordinate half of source q23, on the actual
coupled right contour at every positive diameter. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators Topology
open Set

theorem preferred_comparison_coordinate_center (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (ε τ υ : ℝ) :
    preferredComparisonCoordinate d B ε τ 0 υ 0 =
      preferredArccos (preferredRadialTrace d ε-Complex.cos (-(d.b:ℂ)))-
        (d.b:ℂ)-preferredMovingBranch (IsingBulk.Branch.radialParameter d.alpha ε) := by
  have hb : -d.b ∈ Ioo (-(Real.pi-B.delta)) (-B.delta) := by
    constructor <;> linarith [B.branch_plateau,B.delta_b,d.b_pos]
  obtain ⟨hp,_,_⟩ := B.lower_plateau_jets hb
  have hf : preferredBumpAngle B.m B.p τ 0 υ (-d.b+0) = -(d.b:ℂ) := by
    simp [preferredBumpAngle,hp]
  unfold preferredComparisonCoordinate
  rw [hf]
  simp only [preferredAngularPhase,outwardRadialTrace,preferredRadialTrace,sub_eq_add_neg]

set_option maxHeartbeats 1200000 in
/-- The first q23 estimate holds for all actual occupancies. The P=0 case
uses the proved physical branch-center estimate and true endpoint integration;
the P>0 case uses the actual one-sided bump support. -/
theorem preferred_actual_coordinate_absolute_scale (d : PreferredBranchData)
    (B : PreferredCoareaBump d) :
    ∃ C ε₀ τ₀ δB : ℝ, 0 < C ∧ 0 < ε₀ ∧ 0 < τ₀ ∧ 0 < δB ∧ δB < B.delta ∧
      ∀ (N : ℕ), 0 < N → ∀ ε τ t r : ℝ, 0 < ε → ε < ε₀ → 0 ≤ τ → τ < τ₀ →
      0 < r → ∀ θ : Fin N → ℝ,
      (∀ v, -δB ≤ θ v+d.b ∧ θ v+d.b ≤ d.b+B.delta) →
      (∀ v, t-2*r ≤ θ v+d.b ∧ θ v+d.b ≤ t+2*r) → ∀ i : Fin N,
      ‖preferredSourceCoordinate τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ i‖ ≤
        C*Real.sqrt (|t|+r+ε) := by
  obtain ⟨Cd,εd,τd,δB,hCd,hεd,hτd,hδB,hδBδ,hd⟩ :=
    preferred_fixed_occupancy_coordinate_difference d B
  obtain ⟨Cc,εc,hCc,hεc,hcenter⟩ := preferred_undeformed_center_coordinate_bound d
  obtain ⟨Cp,hCp,hpos⟩ := preferred_actual_coordinate_bound_of_positive_occupancy d B
  let C := Cp+2*(Cd+Cc)
  let ε₀ := min 1 (min εd εc)
  let τ₀ := min 1 τd
  have hC : 0 < C := by dsimp [C]; positivity
  have hε₀ : 0 < ε₀ := lt_min (by norm_num) (lt_min hεd hεc)
  have hτ₀ : 0 < τ₀ := lt_min (by norm_num) hτd
  refine ⟨C,ε₀,τ₀,δB,hC,hε₀,hτ₀,hδB,hδBδ,?_⟩
  intro N hN ε τ t r hε hεr hτ hτr hr θ hbox hwindow i
  have hε1 : ε ≤ 1 := (hεr.trans_le (min_le_left _ _)).le
  have hεd' : ε < εd := hεr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεc' : ε < εc := hεr.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hτ1 : τ ≤ 1 := (hτr.trans_le (min_le_left _ _)).le
  have hτd' : τ < τd := hτr.trans_le (min_le_right _ _)
  have hT : 0 < |t|+r+ε := by positivity
  have hθ (v : Fin N) : θ v ∈ Icc (-Real.pi) Real.pi := by
    have hv := hbox v
    constructor <;> linarith [hv.1,hv.2,B.branch_plateau,B.delta_b,d.b_lt]
  by_cases hP : occupancy B.p θ = 0
  · let υ := occupancy B.m θ/(N:ℝ)
    obtain ⟨_,hυ⟩ := actual_occupancy_box hN B θ
    have hσ : occupancy B.p θ/(N:ℝ) = 0 := by rw [hP,zero_div]
    have heq (a : Fin N) : preferredComparisonCoordinate d B ε τ 0 υ (θ a+d.b) =
        preferredSourceCoordinate τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ a := by
      have hh := preferred_comparison_coordinate_actual d B ε τ θ a
      rw [hσ] at hh
      exact hh
    let u := θ i+d.b
    let ρ := |u|+ε
    have hρ : 0 < ρ := by dsimp [ρ]; positivity
    have hεR : ε ≤ ρ := by dsimp [ρ]; linarith [abs_nonneg u]
    have hboxu : -δB ≤ u ∧ u ≤ d.b+B.delta := hbox i
    have hdiff : ‖preferredComparisonCoordinate d B ε τ 0 υ u-
        preferredComparisonCoordinate d B ε τ 0 υ 0‖ ≤ Cd*ρ/Real.sqrt (ρ+ε) := by
      by_cases hu : 0 ≤ u
      · have hh := hd ε τ 0 υ 0 u 0 ρ hε hεd' hτ hτd' ⟨le_rfl,by norm_num⟩ hυ
          (by linarith) hu hboxu.2 hρ (by linarith) (by dsimp [ρ]; linarith [le_abs_self u])
        simpa only [abs_zero,zero_add] using hh
      · have hh := hd ε τ 0 υ u 0 0 ρ hε hεd' hτ hτd' ⟨le_rfl,by norm_num⟩ hυ
          hboxu.1 (le_of_not_ge hu) (by linarith [d.b_pos,B.delta_pos]) hρ
          (by dsimp [ρ]; linarith [neg_abs_le u]) (by linarith)
        simpa only [abs_zero,zero_add,norm_sub_rev] using hh
    have hquot : ρ/Real.sqrt (ρ+ε) ≤ Real.sqrt ρ := by
      apply (div_le_iff₀ (Real.sqrt_pos.mpr (by positivity : 0 < ρ+ε))).mpr
      have hs := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith : ρ ≤ ρ+ε))
        (Real.sqrt_nonneg ρ)
      nlinarith only [hs,Real.sq_sqrt hρ.le]
    have hdiff' : ‖preferredComparisonCoordinate d B ε τ 0 υ u-
        preferredComparisonCoordinate d B ε τ 0 υ 0‖ ≤ Cd*Real.sqrt ρ := by
      calc
        _ ≤ Cd*ρ/Real.sqrt (ρ+ε) := hdiff
        _ = Cd*(ρ/Real.sqrt (ρ+ε)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hquot hCd.le
    have hzero : ‖preferredComparisonCoordinate d B ε τ 0 υ 0‖ ≤ Cc*Real.sqrt ρ := by
      rw [preferred_comparison_coordinate_center]
      exact (hcenter ε hε hεc').trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hεR) hCc.le)
    have hq : ‖preferredComparisonCoordinate d B ε τ 0 υ u‖ ≤ (Cd+Cc)*Real.sqrt ρ := by
      have hh := norm_add_le
        (preferredComparisonCoordinate d B ε τ 0 υ u-preferredComparisonCoordinate d B ε τ 0 υ 0)
        (preferredComparisonCoordinate d B ε τ 0 υ 0)
      rw [sub_add_cancel] at hh
      nlinarith only [hh,hdiff',hzero]
    have huabs : |u| ≤ |t|+2*r := by
      apply abs_le.mpr
      have hw := hwindow i
      constructor <;> dsimp [u] <;> linarith [le_abs_self t,neg_abs_le t]
    have hρT : ρ ≤ 2*(|t|+r+ε) := by dsimp [ρ]; linarith [abs_nonneg t]
    have hsT : Real.sqrt ρ ≤ 2*Real.sqrt (|t|+r+ε) := by
      have hh := Real.sqrt_le_sqrt (show ρ ≤ 4*(|t|+r+ε) by linarith)
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)] at hh
      norm_num at hh
      exact hh
    rw [← heq i]
    calc
      _ ≤ (Cd+Cc)*Real.sqrt ρ := hq
      _ ≤ (Cd+Cc)*(2*Real.sqrt (|t|+r+ε)) :=
        mul_le_mul_of_nonneg_left hsT (by positivity)
      _ = (2*(Cd+Cc))*Real.sqrt (|t|+r+ε) := by ring
      _ ≤ C*Real.sqrt (|t|+r+ε) :=
        mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (Real.sqrt_nonneg _)
  · have hPpos : 0 < occupancy B.p θ := lt_of_le_of_ne
      (Finset.sum_nonneg (fun a _ => B.lower_bound (θ a))) (Ne.symm hP)
    have hh := hpos N hN ε τ t r hε hε1 hτ hτ1 hr θ hθ hwindow hPpos i
    exact hh.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (Real.sqrt_nonneg _))

end
end IsingBulk.Preferred22
