import IsingBulk.HT22.Transport.FieldNeighborhood.CommonShiftDomain
import IsingBulk.HT22.Tail.ScalarTransport
import IsingBulk.Preferred22.CoordinateScale

/-! Uniform original inverse data on the actual coupled right contour. -/
namespace IsingBulk.HT22
noncomputable section
open Set Metric Geometry IsingBulk.Preferred22 Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- No analytic or jet hypothesis is assumed: the constants and the common
fixed-v convex domain come from the literal inverse and actual occupancies. -/
theorem actual_inverse_uniform_domain_uniform_cap (d : PreferredBranchData) :
    ∃ cap : ℝ, 0<cap ∧ cap<d.alpha ∧ ∀ B : PreferredCoareaBump d,
    ∃ r κ C : ℝ, ∃ D : Set ℂ,
      0<r ∧ 0<κ ∧ 0<C ∧ Convex ℝ D ∧
      (∀ t v : ℂ, ‖t-preferredSelectedPoint d‖≤r → v∈D →
        AnalyticAt ℂ (fun z : ℂ × ℂ => regularInverse z.1 z.2) (t,v) ∧
        ‖sourceInverseT t v‖≤C ∧
        ‖fderiv ℂ (fun z : ℂ × ℂ => sourceInverseV z.1 z.2) (t,v)‖≤C ∧
        ‖fderiv ℂ (fun z : ℂ × ℂ => sourceInverseT z.1 z.2) (t,v)‖≤C) ∧
      (∀ N : ℕ, 0<N → ∀ ε τ : ℝ, |ε|<r → |τ|<r → ∀ θ : Fin N → ℝ,
        (∀ i, -d.b-r≤θ i ∧ θ i≤cap) → ∀ i,
        closedBall (Tail.sourceCoordinate τ B.p B.m
          (IsingBulk.Branch.radialParameter d.alpha ε) θ i) κ ⊆ D) := by
  obtain ⟨cap,ρ,c,D,hcap,hcapa,hρ,hc,hD,hconv,hzero,hgood,hmargin⟩ :=
    preferred_uniform_regular_source_domain_with_margin d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B
  have hz : (0:ℂ)∈D := interior_subset hzero
  have hb : ∀ t∈closedBall (preferredSelectedPoint d) (ρ/2),
      AnalyticAt ℂ preferredMovingBranch t := by
    intro t ht
    have ht' : ‖t-preferredSelectedPoint d‖<ρ := by
      have := (mem_closedBall.mp ht); rw [dist_eq_norm] at this; linarith
    exact (hgood t 0 0 ht' hz hz).1
  have hu : ∀ t∈closedBall (preferredSelectedPoint d) (ρ/2), ∀ q∈D,
      AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (t,q) := by
    intro t ht q hq
    have ht' : ‖t-preferredSelectedPoint d‖<ρ := by
      have := (mem_closedBall.mp ht); rw [dist_eq_norm] at this; linarith
    exact (hgood t q 0 ht' hq hz).2.1
  obtain ⟨C,hC,hbound⟩ := sourceInversePartials_uniform_shift_bound
    (preferredSelectedPoint d) (ρ/2) D hD hb hu
  obtain ⟨κ,r₀,hκ,hr₀,hmargin⟩ := hmargin B.p B.m B.smooth.continuous
    (B.smooth.continuous.comp continuous_neg)
  have hb0 := (hb (preferredSelectedPoint d) (mem_closedBall_self (by positivity))).continuousAt
  obtain ⟨r₁,hr₁,hsmall⟩ := Metric.continuousAt_iff.mp hb0 (κ/4) (by positivity)
  let r := min (ρ/4) (min (r₀/2) (r₁/2))
  have hr : 0<r := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hrρ : r≤ρ/4 := min_le_left _ _
  have hrr₀ : r≤r₀/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hrr₁ : r≤r₁/2 := (min_le_right _ _).trans (min_le_right _ _)
  let T := closedBall (preferredSelectedPoint d) r
  let E := commonShiftDomain T D
  have hsub : T ⊆ closedBall (preferredSelectedPoint d) (ρ/2) := by
    apply closedBall_subset_closedBall
    linarith
  have hbranch : ∀ t∈T, ‖preferredMovingBranch t-preferredMovingBranch (preferredSelectedPoint d)‖<κ/4 := by
    intro t ht
    have hdist : dist t (preferredSelectedPoint d)<r₁ := by
      have := mem_closedBall.mp ht; linarith
    simpa only [dist_eq_norm] using hsmall hdist
  refine ⟨r,κ/2,C,E,hr,by positivity,hC,
    commonShiftDomain_convex T D hconv,?_,?_⟩
  · intro t v ht hv
    have htT : t∈T := by simpa only [T,mem_closedBall,dist_eq_norm] using ht
    have hh := hbound t (v-preferredMovingBranch t) (hsub htT) (hv t htT)
    simpa only [sub_add_cancel] using hh
  · intro N hN ε τ hε hτ θ hθ i
    let t := IsingBulk.Branch.radialParameter d.alpha ε
    let q := preferredSourceCoordinate τ B.p B.m t θ i
    have ht : t∈T := by
      change dist (IsingBulk.Branch.radialParameter d.alpha ε) (preferredSelectedPoint d)≤r
      rw [dist_eq_norm,preferred_radial_distance]
      exact hε.le
    have hq : closedBall q κ ⊆ D := by
      have hmeans := actual_occupancy_box hN B θ
      have hh := hmargin ε τ (occupancy B.p θ/(N:ℝ)) (occupancy B.m θ/(N:ℝ)) (θ i)
        (hε.trans_le (by linarith)) (hτ.trans_le (by linarith)) hmeans.1 hmeans.2
        (by linarith [(hθ i).1]) (hθ i).2
      simpa only [preferredBumpCoordinate_actual] using hh
    have hdiff (s : ℂ) (hs : s∈T) : ‖preferredMovingBranch t-preferredMovingBranch s‖≤κ/2 := by
      have hh := norm_sub_le (preferredMovingBranch t-preferredMovingBranch (preferredSelectedPoint d))
        (preferredMovingBranch s-preferredMovingBranch (preferredSelectedPoint d))
      simp only [sub_sub_sub_cancel_right] at hh
      linarith [hbranch t ht,hbranch s hs]
    have hh := ball_subset_commonShiftDomain T D t q κ hq hdiff
    have he : Tail.sourceCoordinate τ B.p B.m t θ i = q+preferredMovingBranch t := by
      dsimp only [q,Tail.sourceCoordinate,sumCoordinate,physicalPhase,
        preferredSourceCoordinate,preferredSourcePhase]
      ring
    change closedBall (Tail.sourceCoordinate τ B.p B.m t θ i) (κ/2) ⊆ E
    rw [he]
    exact hh

theorem actual_inverse_uniform_domain (d : PreferredBranchData)
    (B : PreferredCoareaBump d) :
    ∃ cap r κ C : ℝ, ∃ D : Set ℂ,
      0<cap ∧ cap<d.alpha ∧ 0<r ∧ 0<κ ∧ 0<C ∧ Convex ℝ D ∧
      (∀ t v : ℂ, ‖t-preferredSelectedPoint d‖≤r → v∈D →
        AnalyticAt ℂ (fun z : ℂ × ℂ => regularInverse z.1 z.2) (t,v) ∧
        ‖sourceInverseT t v‖≤C ∧
        ‖fderiv ℂ (fun z : ℂ × ℂ => sourceInverseV z.1 z.2) (t,v)‖≤C ∧
        ‖fderiv ℂ (fun z : ℂ × ℂ => sourceInverseT z.1 z.2) (t,v)‖≤C) ∧
      (∀ N : ℕ, 0<N → ∀ ε τ : ℝ, |ε|<r → |τ|<r → ∀ θ : Fin N → ℝ,
        (∀ i, -d.b-r≤θ i ∧ θ i≤cap) → ∀ i,
        closedBall (Tail.sourceCoordinate τ B.p B.m
          (IsingBulk.Branch.radialParameter d.alpha ε) θ i) κ ⊆ D) := by
  obtain ⟨cap,hcap,hcapa,hall⟩ := actual_inverse_uniform_domain_uniform_cap d
  obtain ⟨r,κ,C,D,hrest⟩ := hall B
  exact ⟨cap,r,κ,C,D,hcap,hcapa,hrest⟩

end
end IsingBulk.HT22
