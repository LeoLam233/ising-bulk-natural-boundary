import IsingBulk.First.PeriodicYPartition
import IsingBulk.First.LocalizedPartition

/-! Actual construction of fixed compatible y-only cutoffs. The data below
contain only real weights and their proved support properties, never an estimate
or asymptotic conclusion. -/
namespace IsingBulk.First
noncomputable section
open Complex Set Filter Metric
open scoped Topology ContDiff

structure CompatibleYCutoffData (n : ℕ) (alpha beta : ℝ) (U : Set (Fin n → ℝ)) where
  H : ℝ
  delta : ℝ
  H_pos : 0 < H
  delta_pos : 0 < delta
  chi : (Fin n → ℝ) → ℝ
  eta : ℝ → ℝ
  chi_smooth : ContDiff ℝ ∞ chi
  eta_smooth : ContDiff ℝ ∞ eta
  chi_compact : HasCompactSupport chi
  eta_compact : HasCompactSupport eta
  chi_range : ∀ t, 0 ≤ chi t ∧ chi t ≤ 1
  eta_range : ∀ v, 0 ≤ eta v ∧ eta v ≤ 1
  chi_one : chi =ᶠ[𝓝 0] (fun _ => 1)
  chi_support : tsupport chi ⊆ U
  shape_support : ∀ t, chi t ≠ 0 → ∀ j, |shapeExtend t j| < H
  eta_one : ∀ v, |v| ≤ delta → eta v = 1
  eta_support : ∀ v, eta v ≠ 0 → |v| < 2*delta
  small : H+2*delta ≤ 1/2
  separated : 4*(H+2*delta) ≤ ‖exp (-(alpha:ℂ)*I)-exp (-(beta:ℂ)*I)‖

theorem exists_compatibleYCutoffData (n : ℕ) (alpha beta : ℝ)
    (hne : exp (-(alpha:ℂ)*I) ≠ exp (-(beta:ℂ)*I))
    {U : Set (Fin n → ℝ)} (hU : U ∈ 𝓝 (0 : Fin n → ℝ))
    {Hmax Dmax : ℝ} (hH : 0 < Hmax) (hD : 0 < Dmax) :
    ∃ c : CompatibleYCutoffData n alpha beta U, c.H ≤ Hmax ∧ c.delta < Dmax := by
  let sep := ‖exp (-(alpha:ℂ)*I)-exp (-(beta:ℂ)*I)‖
  have hsep : 0 < sep := norm_sub_pos_iff.mpr hne
  let H := min Hmax (min (1/16) (sep/32))
  have hp : 0 < H := lt_min hH (lt_min (by norm_num) (by positivity))
  have hHmax : H ≤ Hmax := min_le_left _ _
  have hHsmall : H ≤ 1/16 := (min_le_right _ _).trans (min_le_left _ _)
  have hHsep : H ≤ sep/32 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨chi,hχ,hχc,hχr,hχ1,hχU,hχs⟩ := exists_fixed_shape_cutoff n hp hU
  obtain ⟨out,hout,houtmax,eta,hη,hηc,hηr,hη1,hηs⟩ := exists_fixed_mean_cutoff (lt_min hD hp)
  have houtH : out < H := houtmax.trans_le (min_le_right _ _)
  have houtD : out < Dmax := houtmax.trans_le (min_le_left _ _)
  let c : CompatibleYCutoffData n alpha beta U := {
    H := H
    delta := out/2
    H_pos := hp
    delta_pos := half_pos hout
    chi := chi
    eta := eta
    chi_smooth := hχ
    eta_smooth := hη
    chi_compact := hχc
    eta_compact := hηc
    chi_range := hχr
    eta_range := hηr
    chi_one := hχ1
    chi_support := hχU
    shape_support := fun t ht => hχs t (subset_closure ht)
    eta_one := hη1
    eta_support := by intro v hv; have hh := hηs v hv; linarith
    small := by linarith
    separated := by change 4*(H+2*(out/2)) ≤ sep; linarith }
  exact ⟨c,hHmax,by dsimp [c]; linarith⟩

namespace CompatibleYCutoffData
variable {n : ℕ} {alpha beta : ℝ} {U : Set (Fin n → ℝ)}

def leftWeight (c : CompatibleYCutoffData n alpha beta U) := fixedYChartWeight alpha c.chi c.eta

def rightWeight (c : CompatibleYCutoffData n alpha beta U) := fixedYChartWeight beta c.chi c.eta

def remainder (c : CompatibleYCutoffData n alpha beta U) := fixedYComplement alpha beta c.chi c.eta

theorem eta_one_near (c : CompatibleYCutoffData n alpha beta U) : c.eta =ᶠ[𝓝 0] (fun _ => 1) := by
  filter_upwards [ball_mem_nhds (0:ℝ) c.delta_pos] with v hv
  have hv' : |v| < c.delta := by simpa only [mem_ball,Real.dist_eq,sub_zero] using hv
  exact c.eta_one v hv'.le

theorem disjoint (c : CompatibleYCutoffData n alpha beta U) (theta : Fin (n+1) → ℝ) :
    c.leftWeight theta ≠ 0 → c.rightWeight theta = 0 :=
  fixedYChartWeight_disjoint alpha beta (by linarith [c.small]) c.separated c.shape_support c.eta_support theta

theorem left_smooth (c : CompatibleYCutoffData n alpha beta U) : ContDiff ℝ ∞ c.leftWeight :=
  fixedYChartWeight_contDiff alpha c.chi_smooth c.eta_smooth

theorem right_smooth (c : CompatibleYCutoffData n alpha beta U) : ContDiff ℝ ∞ c.rightWeight :=
  fixedYChartWeight_contDiff beta c.chi_smooth c.eta_smooth

theorem remainder_smooth (c : CompatibleYCutoffData n alpha beta U) : ContDiff ℝ ∞ c.remainder :=
  fixedYComplement_contDiff alpha beta c.chi_smooth c.eta_smooth

theorem partition (c : CompatibleYCutoffData n alpha beta U) (theta : Fin (n+1) → ℝ) :
    c.leftWeight theta+c.rightWeight theta+c.remainder theta = 1 := by
  unfold leftWeight rightWeight remainder fixedYComplement
  ring

theorem remainder_excludes_left (c : CompatibleYCutoffData n alpha beta U)
    {theta : Fin (n+1) → ℝ} (hc : ∀ j, exp (((theta j+alpha:ℝ):ℂ)*I)=1) :
    theta ∉ tsupport c.remainder :=
  fixedYComplement_excludes_center alpha beta c.chi_one c.eta_one_near c.disjoint hc

theorem remainder_excludes_right (c : CompatibleYCutoffData n alpha beta U)
    {theta : Fin (n+1) → ℝ} (hc : ∀ j, exp (((theta j+beta:ℝ):ℂ)*I)=1) :
    theta ∉ tsupport c.remainder := by
  have hd : ∀ t, fixedYChartWeight beta c.chi c.eta t ≠ 0 → fixedYChartWeight alpha c.chi c.eta t = 0 := by
    intro t ht
    by_contra ha
    exact ht (c.disjoint t ha)
  have he : c.remainder = fixedYComplement beta alpha c.chi c.eta := by
    funext t
    unfold remainder fixedYComplement
    ring
  rw [he]
  exact fixedYComplement_excludes_center beta alpha c.chi_one c.eta_one_near hd hc

/-- The same constructed weights work at every admissible source parameter
and fixed contour radius; all x variables remain unweighted. -/
theorem actual_integral_partition (c : CompatibleYCutoffData n alpha beta U)
    (r : ℝ) (s : ℂ) (z : ℂ → ℂ)
    (h : ∀ theta : Fin (n+1) → ℝ, ResidueAdmissible r s (angleTuple r theta)
      (fun i => z (anglePoint r (theta i)))) :
    doubleFormFactor (n+1) r s = weightedDoubleFormFactor (n+1) r s c.leftWeight +
      weightedDoubleFormFactor (n+1) r s c.rightWeight +
      localizedDoubleFormFactor (n+1) r s (fun p => c.remainder p.2) :=
  compatible_localization_identity (n+1) (Nat.succ_pos n) r s z h c.leftWeight c.rightWeight
    c.left_smooth.continuous c.right_smooth.continuous

end CompatibleYCutoffData
end
end IsingBulk.First
