import IsingBulk.Tail.NestedCutoffs
import IsingBulk.Tail.SelectedFDiskSupport
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Fixed smooth real L/R/B labels built from limiting dispersion. The sign
seam is removed by an actual branch plateau, rather than assuming a smooth
partition across a discontinuous sign test. Upper-branch exclusion on actual
selector/current support is a separate source attachment. -/
namespace IsingBulk.Tail
noncomputable section
open Set Filter Function
open scoped Topology ContDiff BigOperators

def splitPositive (chi : ℝ → ℝ) (t : ℝ) : ℝ := if 0 < t then 1-chi t else 0

def splitNegative (chi : ℝ → ℝ) (t : ℝ) : ℝ := if t < 0 then 1-chi t else 0

theorem splitPositive_smooth (chi : ℝ → ℝ) (hchi : ContDiff ℝ ∞ chi)
    {r : ℝ} (hr : 0 < r) (hplateau : ∀ t, |t| < r → chi t=1) :
    ContDiff ℝ ∞ (splitPositive chi) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  rcases lt_trichotomy t 0 with ht|rfl|ht
  · apply (show ContDiffAt ℝ ∞ (fun _ : ℝ => (0:ℝ)) t from contDiffAt_const).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds ht] with u hu
    simp [splitPositive,not_lt.mpr hu.le]
  · apply (show ContDiffAt ℝ ∞ (fun _ : ℝ => (0:ℝ)) 0 from contDiffAt_const).congr_of_eventuallyEq
    have hh : ∀ᶠ u : ℝ in 𝓝 0, |u| < r := by
      filter_upwards [Metric.ball_mem_nhds (0:ℝ) hr] with u hu
      simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hu
    filter_upwards [hh] with u hu
    simp [splitPositive,hplateau u hu]
  · apply (show ContDiffAt ℝ ∞ (fun u => 1-chi u) t from
      contDiffAt_const.sub hchi.contDiffAt).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds ht] with u hu
    simp only [splitPositive,ite_eq_left hu]

theorem splitNegative_smooth (chi : ℝ → ℝ) (hchi : ContDiff ℝ ∞ chi)
    {r : ℝ} (hr : 0 < r) (hplateau : ∀ t, |t| < r → chi t=1) :
    ContDiff ℝ ∞ (splitNegative chi) := by
  have hp := splitPositive_smooth (fun t => chi (-t)) (hchi.comp contDiff_neg) hr
    (fun t ht => hplateau (-t) (by simpa only [abs_neg] using ht))
  convert hp.comp contDiff_neg using 1
  funext t
  simp [splitPositive,splitNegative]

theorem branch_sign_partition {delta : ℝ} (hd : 0 < delta) (t : ℝ) :
    splitPositive (fixedBranchBump delta hd) t + splitNegative (fixedBranchBump delta hd) t +
      fixedBranchBump delta hd t = 1 := by
  rcases lt_trichotomy t 0 with ht|rfl|ht
  · simp [splitPositive,splitNegative,ht,not_lt.mpr ht.le]
  · rw [fixedBranchBump_one delta hd (by simp; positivity)]
    simp [splitPositive,splitNegative]
  · simp [splitPositive,splitNegative,ht,not_lt.mpr ht.le]

def sectorDisplacement (b theta : ℝ) : ℝ := Real.cos b-Real.cos theta

def sectorBranch (b delta : ℝ) (hd : 0 < delta) (theta : ℝ) : ℝ :=
  fixedBranchBump delta hd (sectorDisplacement b theta)

def sectorLeft (b delta : ℝ) (hd : 0 < delta) (theta : ℝ) : ℝ :=
  splitPositive (fixedBranchBump delta hd) (sectorDisplacement b theta)

def sectorRight (b delta : ℝ) (hd : 0 < delta) (theta : ℝ) : ℝ :=
  splitNegative (fixedBranchBump delta hd) (sectorDisplacement b theta)

theorem sector_partition (b delta : ℝ) (hd : 0 < delta) (theta : ℝ) :
    sectorLeft b delta hd theta+sectorRight b delta hd theta+sectorBranch b delta hd theta=1 :=
  branch_sign_partition hd _

theorem sector_labels_smooth (b delta : ℝ) (hd : 0 < delta) :
    ContDiff ℝ ∞ (sectorLeft b delta hd) ∧ ContDiff ℝ ∞ (sectorRight b delta hd) ∧
      ContDiff ℝ ∞ (sectorBranch b delta hd) := by
  have hp : ∀ t, |t| < delta/2 → fixedBranchBump delta hd t=1 :=
    fun t ht => fixedBranchBump_one delta hd ht.le
  have hc : ContDiff ℝ ∞ (sectorDisplacement b) := contDiff_const.sub Real.contDiff_cos
  exact ⟨(splitPositive_smooth _ (fixedBranchBump delta hd).contDiff (half_pos hd) hp).comp hc,
    (splitNegative_smooth _ (fixedBranchBump delta hd).contDiff (half_pos hd) hp).comp hc,
    (fixedBranchBump delta hd).contDiff.comp hc⟩

theorem sector_labels_nonnegative (b delta : ℝ) (hd : 0 < delta) (theta : ℝ) :
    0 ≤ sectorLeft b delta hd theta ∧ 0 ≤ sectorRight b delta hd theta ∧
      0 ≤ sectorBranch b delta hd theta := by
  have hh : fixedBranchBump delta hd (sectorDisplacement b theta) ≤ 1 :=
    (fixedBranchBump delta hd).le_one
  refine ⟨?_,?_,(fixedBranchBump delta hd).nonneg⟩
  · unfold sectorLeft splitPositive
    split_ifs <;> linarith
  · unfold sectorRight splitNegative
    split_ifs <;> linarith

theorem sector_labels_periodic (b delta : ℝ) (hd : 0 < delta) :
    Function.Periodic (sectorLeft b delta hd) (2*Real.pi) ∧
    Function.Periodic (sectorRight b delta hd) (2*Real.pi) ∧
    Function.Periodic (sectorBranch b delta hd) (2*Real.pi) := by
  simp only [Function.Periodic,sectorLeft,sectorRight,sectorBranch,sectorDisplacement,Real.cos_add_two_pi,
    forall_const]
  exact ⟨trivial,trivial,trivial⟩


theorem sectorDisplacement_zero_lower {b theta : ℝ} (hb : 0 < b) (hbpi : b < Real.pi)
    (ht0 : 0 ≤ theta) (htpi : theta ≤ 2*Real.pi)
    (hsin : Real.sin theta ≤ Real.sin b/2) (hzero : sectorDisplacement b theta=0) :
    theta=2*Real.pi-b := by
  have hcos : Real.cos theta=Real.cos b := by unfold sectorDisplacement at hzero; linarith
  have hsb : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi hb hbpi
  have hsquare : Real.sin theta^2=Real.sin b^2 := by
    have ht := Real.sin_sq_add_cos_sq theta
    rw [hcos] at ht
    linarith [Real.sin_sq_add_cos_sq b]
  have hprod : (Real.sin theta-Real.sin b)*(Real.sin theta+Real.sin b)=0 := by nlinarith
  have hsneg : Real.sin theta= -Real.sin b := by
    rcases mul_eq_zero.mp hprod with hp|hp <;> linarith
  apply lowerChord_zero_angle hb hbpi ht0 htpi
  norm_num [lowerChord,hcos,hsneg]

theorem sector_branch_angular_width {b h : ℝ} (hb : 0 < b) (hbpi : b < Real.pi)
    (hh : 0 < h) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ ∀ theta : ℝ, 0 ≤ theta → theta ≤ 2*Real.pi →
      Real.sin theta ≤ Real.sin b/2 → |sectorDisplacement b theta| ≤ delta0 →
      |theta+b-2*Real.pi| < h := by
  let K : Set ℝ := Icc 0 (2*Real.pi) ∩ {theta | Real.sin theta ≤ Real.sin b/2} ∩
    {theta | h ≤ |theta+b-2*Real.pi|}
  have hK : IsCompact K :=
    (isCompact_Icc.inter_right (isClosed_le Real.continuous_sin continuous_const)).inter_right
      (isClosed_le continuous_const (by fun_prop))
  have hc : Continuous (fun theta => |sectorDisplacement b theta|) := by
    unfold sectorDisplacement
    fun_prop
  by_cases hn : K.Nonempty
  · obtain ⟨theta,htheta,hmin⟩ := hK.exists_isMinOn hn hc.continuousOn
    have hp : 0 < |sectorDisplacement b theta| := by
      apply abs_pos.mpr
      intro hz
      have he := sectorDisplacement_zero_lower hb hbpi htheta.1.1.1 htheta.1.1.2 htheta.1.2 hz
      have hh' : h ≤ |theta+b-2*Real.pi| := htheta.2
      rw [he,show 2*Real.pi-b+b-2*Real.pi=0 by ring,abs_zero] at hh'
      linarith
    refine ⟨|sectorDisplacement b theta|/2,half_pos hp,?_⟩
    intro u hu0 hupi hsin hdisp
    by_contra hout
    have hmem : u ∈ K := ⟨⟨⟨hu0,hupi⟩,hsin⟩,le_of_not_gt hout⟩
    have hm : |sectorDisplacement b theta| ≤ |sectorDisplacement b u| := hmin hmem
    linarith
  · refine ⟨1,by norm_num,?_⟩
    intro theta ht0 htpi hsin _hdisp
    by_contra hout
    exact hn ⟨theta,⟨⟨⟨ht0,htpi⟩,hsin⟩,le_of_not_gt hout⟩⟩



theorem sector_labels_tsupport (b delta : ℝ) (hd : 0 < delta) :
    tsupport (sectorLeft b delta hd) ⊆ {theta | delta/2 ≤ sectorDisplacement b theta} ∧
    tsupport (sectorRight b delta hd) ⊆ {theta | sectorDisplacement b theta ≤ -delta/2} ∧
    tsupport (sectorBranch b delta hd) ⊆ {theta | |sectorDisplacement b theta| ≤ delta} := by
  have hc : Continuous (sectorDisplacement b) := by unfold sectorDisplacement; fun_prop
  refine ⟨closure_minimal ?_ (isClosed_le continuous_const hc),
    closure_minimal ?_ (isClosed_le hc continuous_const),
    closure_minimal ?_ (isClosed_le hc.abs continuous_const)⟩
  · intro theta htheta
    change splitPositive (fixedBranchBump delta hd) (sectorDisplacement b theta) ≠ 0 at htheta
    have ht : 0 < sectorDisplacement b theta := by
      by_contra hh
      simp [splitPositive,hh] at htheta
    by_contra hn
    have hm : |sectorDisplacement b theta| ≤ delta/2 := by
      rw [abs_of_pos ht]
      exact (lt_of_not_ge hn).le
    simp [splitPositive,fixedBranchBump_one delta hd hm] at htheta
  · intro theta htheta
    change splitNegative (fixedBranchBump delta hd) (sectorDisplacement b theta) ≠ 0 at htheta
    have ht : sectorDisplacement b theta < 0 := by
      by_contra hh
      simp [splitNegative,hh] at htheta
    by_contra hn
    have hm : |sectorDisplacement b theta| ≤ delta/2 := by
      rw [abs_of_neg ht]
      have hh : -delta/2 < sectorDisplacement b theta :=
        lt_of_not_ge (show ¬ sectorDisplacement b theta ≤ -delta/2 from hn)
      linarith
    simp [splitNegative,fixedBranchBump_one delta hd hm] at htheta
  · intro theta htheta
    exact (fixedBranchBump_support delta hd htheta).le

theorem sectorDisplacement_lower_bound (b u : ℝ) :
    |sectorDisplacement b (-b+u)| ≤ |u| := by
  have hh := Real.abs_cos_sub_cos_le (-b) (-b+u)
  simpa only [sectorDisplacement,Real.cos_neg,show -b-(-b+u)= -u by ring,abs_neg] using hh

theorem sectorBranch_lower_plateau (b delta : ℝ) (hd : 0 < delta) {u : ℝ}
    (hu : |u| ≤ delta/2) : sectorBranch b delta hd (-b+u)=1 :=
  fixedBranchBump_one delta hd ((sectorDisplacement_lower_bound b u).trans hu)

theorem sector_branch_support_lower_chart {b h : ℝ} (hb : 0 < b) (hbpi : b < Real.pi)
    (hh : 0 < h) : ∃ delta0 : ℝ, 0 < delta0 ∧ ∀ delta : ℝ, ∀ hd : 0 < delta,
      delta ≤ delta0 → ∀ theta : ℝ, 0 ≤ theta → theta ≤ 2*Real.pi →
      Real.sin theta ≤ Real.sin b/2 → theta ∈ tsupport (sectorBranch b delta hd) →
      |theta+b-2*Real.pi| < h := by
  obtain ⟨delta0,hd0,hwidth⟩ := sector_branch_angular_width hb hbpi hh
  refine ⟨delta0,hd0,?_⟩
  intro delta hd hdelta theta ht0 htpi hsin hsupport
  exact hwidth theta ht0 htpi hsin (((sector_labels_tsupport b delta hd).2.2 hsupport).trans hdelta)

theorem sector_label_finite_jets_support (b delta : ℝ) (hd : 0 < delta) (j : ℕ) :
    tsupport (iteratedFDeriv ℝ j (sectorLeft b delta hd)) ⊆
      {theta | delta/2 ≤ sectorDisplacement b theta} ∧
    tsupport (iteratedFDeriv ℝ j (sectorRight b delta hd)) ⊆
      {theta | sectorDisplacement b theta ≤ -delta/2} ∧
    tsupport (iteratedFDeriv ℝ j (sectorBranch b delta hd)) ⊆
      {theta | |sectorDisplacement b theta| ≤ delta} := by
  obtain ⟨hL,hR,hB⟩ := sector_labels_tsupport b delta hd
  exact ⟨(tsupport_iteratedFDeriv_subset j).trans hL,
    (tsupport_iteratedFDeriv_subset j).trans hR,(tsupport_iteratedFDeriv_subset j).trans hB⟩

end
end IsingBulk.Tail
