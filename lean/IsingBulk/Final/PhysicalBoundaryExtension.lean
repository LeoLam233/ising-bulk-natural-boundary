import IsingBulk.Final.PhysicalGerm
import IsingBulk.Final.ExteriorCrescent
import IsingBulk.Final.InverseTemperatureSheets
import IsingBulk.Final.InverseTemperatureLocalBranches

/-! A boundary-continuation candidate for the actual physical branch family.
The inverse temperature need only exist on an arbitrary open exterior set
approaching the boundary, not on a fictitious globally single-valued sheet.
Normalization is the literal source chi=beta*X. -/
namespace IsingBulk.Final
noncomputable section
open Set Filter Metric IsingBulk.Tail
open scoped Topology

def physicalHalfPlane (sigma : ℝ) : Set ℂ := {s | 0 < sigma*s.re}

def HasPhysicalBoundaryExtension (J : ℝ) (X : ℂ → ℂ) (z : ℂ) : Prop :=
  ∃ R : ℝ, 0 < R ∧ ∃ U : Set ℂ, IsOpen U ∧ z ∈ closure U ∧
    U ⊆ exteriorCrescent z R ∧ ∃ beta g : ℂ → ℂ,
      AnalyticOnNhd ℂ beta U ∧ AnalyticOnNhd ℂ g (ball z R) ∧
      (∀ s ∈ U, Complex.sinh (2*(J:ℂ)*beta s)=s) ∧ EqOn g (fun s => beta s*X s) U

theorem physicalHalfPlane_isOpen (sigma : ℝ) : IsOpen (physicalHalfPlane sigma) :=
  isOpen_lt continuous_const (continuous_const.mul Complex.continuous_re)

theorem physicalHalfPlane_convex (sigma : ℝ) : Convex ℝ (physicalHalfPlane sigma) := by
  intro x hx y hy a b ha hb hab
  change 0 < sigma*(a • x+b • y).re
  simp only [Complex.add_re,Complex.smul_re,smul_eq_mul]
  have hx' : 0 < sigma*x.re := hx
  have hy' : 0 < sigma*y.re := hy
  by_cases ha0 : a=0
  · have hb1 : b=1 := by linarith
    simpa only [ha0,hb1,zero_mul,one_mul,zero_add] using hy'
  · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have h1 := mul_pos hap hx'
    have h2 := mul_nonneg hb hy'.le
    nlinarith

theorem physicalHalfPlane_canonical {J sigma : ℝ} (hJ : 0 < J) (hsigma : sigma^2=1) :
    ∃ beta0 : ℂ → ℂ, AnalyticOnNhd ℂ beta0 (physicalHalfPlane sigma) ∧
      ∀ s ∈ physicalHalfPlane sigma, Complex.sinh (2*(J:ℂ)*beta0 s)=s := by
  rcases sq_eq_one_iff.mp hsigma with rfl|rfl
  · refine ⟨inverseTemperatureBranch J,?_,?_⟩
    · intro s hs
      exact (inverseTemperatureBranch_regular (by simpa only [physicalHalfPlane,mem_ofPred_eq,one_mul] using hs) hJ).1
    · intro s hs
      exact inverseTemperatureBranch_relation (by simpa only [physicalHalfPlane,mem_ofPred_eq,one_mul] using hs) hJ
  · refine ⟨inverseTemperatureLeft J,?_,?_⟩
    · intro s hs
      have hr : s.re < 0 := by change 0 < (-1)*s.re at hs; linarith
      exact (inverseTemperatureLeft_regular hr hJ).1
    · intro s hs
      have hr : s.re < 0 := by change 0 < (-1)*s.re at hs; linarith
      exact inverseTemperatureLeft_relation hr hJ

theorem open_nonempty_nonaxis {U : Set ℂ} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ s ∈ U, s.re ≠ 0 := by
  obtain ⟨s,hs⟩ := hne
  by_cases hr : s.re=0
  · obtain ⟨d,hd,hdU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hs)
    refine ⟨s+(d/2:ℝ),hdU ?_,?_⟩
    · rw [mem_ball_iff_norm]
      simp only [add_sub_cancel_left,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (half_pos hd)]
      linarith
    · simp only [Complex.add_re,Complex.ofReal_re,hr,zero_add]
      exact (half_pos hd).ne'
  · exact ⟨s,hs,hr⟩

theorem ball_subset_physicalHalfPlane {z : ℂ} {r sigma : ℝ}
    (hsigma : sigma^2=1) (hz : 0 < sigma*z.re) (hr : r ≤ sigma*z.re/2) :
    ball z r ⊆ physicalHalfPlane sigma := by
  have hsigabs : |sigma|=1 := by nlinarith [sq_abs sigma,abs_nonneg sigma]
  intro s hs
  have hn := mem_ball_iff_norm.mp hs
  have hh : |s.re-z.re| < r := by
    have hh' : |s.re-z.re| ≤ ‖s-z‖ := by
      simpa only [Complex.sub_re] using Complex.abs_re_le_norm (s-z)
    exact hh'.trans_lt hn
  have hm : |sigma*(s.re-z.re)| < r := by rw [abs_mul,hsigabs,one_mul]; exact hh
  have hl := (abs_lt.mp hm).1
  change 0 < sigma*s.re
  nlinarith

theorem half_crescent_candidate_contradiction {X : ℂ → ℂ}
    (hXa : AnalyticOnNhd ℂ X {s : ℂ | 1 < ‖s‖})
    (hX : ∀ w : ℂ, ‖w‖=1 → ¬ HasExteriorExtension X w)
    {J sigma R r : ℝ} (hJ : 0 < J) (hsigma : sigma^2=1) {z w : ℂ}
    (hrR : r ≤ R) (hw : ‖w‖=1) (hwb : w ∈ ball z r ∩ physicalHalfPlane sigma)
    {U : Set ℂ} (hU : IsOpen U) (beta g : ℂ → ℂ)
    (hb : AnalyticOnNhd ℂ beta U) (hg : AnalyticOnNhd ℂ g (ball z R))
    (hrel : ∀ s ∈ U, Complex.sinh (2*(J:ℂ)*beta s)=s)
    (hEq : EqOn g (fun s => beta s*X s) U)
    (hD : IsPreconnected (exteriorCrescent z r ∩ physicalHalfPlane sigma))
    (hseed : (U ∩ (exteriorCrescent z r ∩ physicalHalfPlane sigma)).Nonempty) : False := by
  let D := exteriorCrescent z r ∩ physicalHalfPlane sigma
  obtain ⟨s0,hs0⟩ := hseed
  have hOpen : IsOpen (U ∩ D) := hU.inter ((exteriorCrescent_isOpen z r).inter (physicalHalfPlane_isOpen sigma))
  obtain ⟨d,hd,hdsub⟩ := Metric.mem_nhds_iff.mp (hOpen.mem_nhds hs0)
  have hballU : ball s0 d ⊆ U := fun s hs => (hdsub hs).1
  have hballD : ball s0 d ⊆ D := fun s hs => (hdsub hs).2
  obtain ⟨beta0,hb0,hrel0⟩ := physicalHalfPlane_canonical hJ hsigma
  obtain ⟨betaExt,hbe,hbee,hber,hben⟩ := inverseTemperature_sheet_extension isOpen_ball
    (convex_ball s0 d).isPreconnected ⟨s0,mem_ball_self hd⟩
    (fun s hs => (hballD hs).2) (physicalHalfPlane_convex sigma).isPreconnected hJ beta beta0
    (hb.mono hballU) hb0 (fun s hs => hrel s (hballU hs)) hrel0
  have hgD : AnalyticOnNhd ℂ g D := fun s hs => hg s ((ball_subset_ball hrR) hs.1.1)
  have hxD : AnalyticOnNhd ℂ (fun s => betaExt s*X s) D :=
    fun s hs => (hbe s hs.2).mul (hXa s hs.1.2)
  have heq : g =ᶠ[𝓝 s0] (fun s => betaExt s*X s) := by
    filter_upwards [ball_mem_nhds s0 hd] with s hs
    rw [hEq (hballU hs),hbee hs]
  have hfull : EqOn g (fun s => betaExt s*X s) D :=
    hgD.eqOn_of_preconnected_of_eventuallyEq hxD hD hs0.2 heq
  have hext : HasExteriorExtension (fun s => betaExt s*X s) w := by
    refine ⟨ball z r ∩ physicalHalfPlane sigma,isOpen_ball.inter (physicalHalfPlane_isOpen sigma),
      hwb,g,?_,?_⟩
    · intro s hs
      exact hg s ((ball_subset_ball hrR) hs.1)
    · intro s hs
      exact hfull ⟨⟨hs.1.1,hs.2⟩,hs.1.2⟩
  have hw0 : w ≠ 0 := by intro he; simp [he] at hw
  exact hX w hw (extension_of_analytic_factor_extension (hbe w hwb.2) (hben w hwb.2 hw0) hext)


theorem physical_no_boundary_extension {X : ℂ → ℂ}
    (hXa : AnalyticOnNhd ℂ X {s : ℂ | 1 < ‖s‖})
    (hX : ∀ w : ℂ, ‖w‖=1 → ¬ HasExteriorExtension X w)
    {J : ℝ} (hJ : 0 < J) :
    ∀ z : ℂ, ‖z‖=1 → ¬ HasPhysicalBoundaryExtension J X z := by
  intro z hz hc
  obtain ⟨R,hR,U,hU,hzU,hsub,beta,g,hb,hg,hrel,hEq⟩ := hc
  have hnear (r : ℝ) (hr : 0 < r) : (U ∩ ball z r).Nonempty := by
    have hh := mem_closure_iff_nhds.mp hzU (ball z r) (ball_mem_nhds z hr)
    simpa only [inter_comm] using hh
  have hsign {w : ℂ} (hw : w.re ≠ 0) : ∃ sigma : ℝ, sigma^2=1 ∧ 0 < sigma*w.re := by
    rcases lt_or_gt_of_ne hw with hl|hr
    · exact ⟨-1,by norm_num,by linarith⟩
    · exact ⟨1,by norm_num,by simpa only [one_mul] using hr⟩
  by_cases haxis : z.re=0
  · let r := min R (1/2)
    have hr : 0 < r := lt_min hR (by norm_num)
    have hrR : r ≤ R := min_le_left _ _
    have hrs : r ≤ 1/2 := min_le_right _ _
    obtain ⟨s0,hs0,hs0re⟩ := open_nonempty_nonaxis (hU.inter isOpen_ball) (hnear r hr)
    obtain ⟨sigma,hsigma,hsign0⟩ := hsign hs0re
    obtain ⟨w,hw,hwb,hwh⟩ := axis_unit_point_near hz haxis hr hsigma
    have hconn : IsPreconnected (exteriorCrescent z r ∩ physicalHalfPlane sigma) :=
      (axisCrescent_half_isConnected hz haxis hr hrs hsigma).isPreconnected
    apply half_crescent_candidate_contradiction hXa hX hJ hsigma hrR hw ⟨hwb,hwh⟩
      hU beta g hb hg hrel hEq hconn
    exact ⟨s0,hs0.1,⟨⟨hs0.2,(hsub hs0.1).2⟩,hsign0⟩⟩
  · obtain ⟨sigma,hsigma,hzhalf⟩ := hsign haxis
    let r := min R (min (1/2) (sigma*z.re/2))
    have hr : 0 < r := lt_min hR (lt_min (by norm_num) (half_pos hzhalf))
    have hrR : r ≤ R := min_le_left _ _
    have hrs : r ≤ 1/2 := (min_le_right _ _).trans (min_le_left _ _)
    have hrz : r ≤ sigma*z.re/2 := (min_le_right _ _).trans (min_le_right _ _)
    have hball := ball_subset_physicalHalfPlane hsigma hzhalf hrz
    have heq : exteriorCrescent z r ∩ physicalHalfPlane sigma=exteriorCrescent z r :=
      inter_eq_left.mpr (fun s hs => hball hs.1)
    have hconn : IsPreconnected (exteriorCrescent z r ∩ physicalHalfPlane sigma) := by
      rw [heq]
      exact (exteriorCrescent_isConnected hz hr hrs).isPreconnected
    apply half_crescent_candidate_contradiction hXa hX hJ hsigma hrR hz ⟨mem_ball_self hr,hzhalf⟩
      hU beta g hb hg hrel hEq hconn
    obtain ⟨s0,hsU,hsB⟩ := hnear r hr
    exact ⟨s0,hsU,⟨⟨hsB,(hsub hsU).2⟩,hball hsB⟩⟩


/-- Any ordinary extension of an actual local inverse-temperature chart is
included in the branch-independent continuation predicate. -/
theorem physical_boundary_extension_of_chart {J : ℝ} {X beta : ℂ → ℂ} {z : ℂ}
    (hz : ‖z‖=1) (hb : AnalyticAt ℂ beta z)
    (hrel : ∀ᶠ s in 𝓝 z, Complex.sinh (2*(J:ℂ)*beta s)=s)
    (he : HasExteriorExtension (fun s => beta s*X s) z) :
    HasPhysicalBoundaryExtension J X z := by
  obtain ⟨V,hV,hzV,g,hg,hEq⟩ := he
  have hnear : ∀ᶠ s in 𝓝 z, s ∈ V ∧ AnalyticAt ℂ beta s ∧
      Complex.sinh (2*(J:ℂ)*beta s)=s := (show ∀ᶠ s in 𝓝 z, s ∈ V from hV.mem_nhds hzV).and (hb.eventually_analyticAt.and hrel)
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨r,hr,exteriorCrescent z r,exteriorCrescent_isOpen z r,
    unit_mem_closure_exteriorCrescent hz hr,Subset.rfl,beta,g,?_,?_,?_,?_⟩
  · intro s hs
    exact (hsub hs.1).2.1
  · intro s hs
    exact hg s (hsub hs).1
  · intro s hs
    exact (hsub hs.1).2.2
  · intro s hs
    exact hEq ⟨(hsub hs.1).1,hs.2⟩

end
end IsingBulk.Final
