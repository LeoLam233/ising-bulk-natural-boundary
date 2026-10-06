import IsingBulk.First.DoublePeriodicBump
import IsingBulk.First.SmoothCutoffConstruction

/-! A finite family of genuine compact lifted smooth bumps covers any compact
set of regular torus lifts after periodicization. -/
namespace IsingBulk.First
noncomputable section
open Set Metric Filter
open scoped Topology ContDiff BigOperators

theorem doubleCenteredWrap_self {N : ℕ} (c : DoubleAngularVector N) : doubleCenteredWrap c c = c := by
  have hx : centeredWrap c.1 c.1 = c.1 := centeredWrap_eq
    (fun _ => ⟨by simp; exact Real.pi_pos,by simp; exact Real.pi_pos.le⟩)
  have hy : centeredWrap c.2 c.2 = c.2 := centeredWrap_eq
    (fun _ => ⟨by simp; exact Real.pi_pos,by simp; exact Real.pi_pos.le⟩)
  simp only [doubleCenteredWrap,hx,hy]

theorem double_norm_coordinate_bound {N : ℕ} (x c : DoubleAngularVector N) (i : Fin N) :
    |x.1 i-c.1 i| ≤ ‖x-c‖ ∧ |x.2 i-c.2 i| ≤ ‖x-c‖ := by
  change |x.1 i-c.1 i| ≤ max ‖x.1-c.1‖ ‖x.2-c.2‖ ∧
    |x.2 i-c.2 i| ≤ max ‖x.1-c.1‖ ‖x.2-c.2‖
  have h1 : |x.1 i-c.1 i| ≤ ‖x.1-c.1‖ := by
    simpa only [Pi.sub_apply,Real.norm_eq_abs] using norm_le_pi_norm (x.1-c.1) i
  have h2 : |x.2 i-c.2 i| ≤ ‖x.2-c.2‖ := by
    simpa only [Pi.sub_apply,Real.norm_eq_abs] using norm_le_pi_norm (x.2-c.2) i
  exact ⟨h1.trans (le_max_left _ _),h2.trans (le_max_right _ _)⟩

theorem finite_torus_bump_cover {N : ℕ} {K : Set (DoubleAngularVector N)}
    (hK : IsCompact K) (radius : K → ℝ) (hr : ∀ c, 0 < radius c) :
    ∃ (S : Finset K) (b : K → DoubleAngularVector N → ℝ),
      (∀ c, ContDiff ℝ ∞ (b c) ∧ HasCompactSupport (b c) ∧
        (∀ u, 0 ≤ b c u ∧ b c u ≤ 1) ∧
        tsupport (b c) ⊆ closedBall (c:DoubleAngularVector N) (radius c) ∧
        (∀ u, b c u ≠ 0 → ∀ i, |u.1 i-c.1.1 i| ≤ 1/2 ∧ |u.2 i-c.1.2 i| ≤ 1/2)) ∧
      (∀ u ∈ K, 0 < ∑ c ∈ S, doublePeriodicizeBump (c:DoubleAngularVector N) (b c) u) := by
  classical
  have hex (c : K) := exists_fixed_smooth_cutoff (c:DoubleAngularVector N)
    (ball_mem_nhds (c:DoubleAngularVector N) (lt_min (hr c) (by norm_num : (0:ℝ)<1/4)))
  choose b hb hcomp hnonneg hone hsupp using hex
  have hsmall (c : K) (u : DoubleAngularVector N) (hu : b c u ≠ 0) (i : Fin N) :
      |u.1 i-c.1.1 i| ≤ 1/2 ∧ |u.2 i-c.1.2 i| ≤ 1/2 := by
    have hdist : dist u (c:DoubleAngularVector N) < min (radius c) (1/4) :=
      hsupp c (subset_closure hu)
    rw [dist_eq_norm] at hdist
    have hx := double_norm_coordinate_bound u (c:DoubleAngularVector N) i
    have hmin := min_le_right (radius c) (1/4)
    constructor <;> linarith [hx.1,hx.2]
  have hper (c : K) : ContDiff ℝ ∞ (doublePeriodicizeBump (c:DoubleAngularVector N) (b c)) :=
    doublePeriodicizeBump_contDiff _ _ (hb c) (hsmall c)
  have hcover : K ⊆ ⋃ c : K, {u | 0 < doublePeriodicizeBump (c:DoubleAngularVector N) (b c) u} := by
    intro u hu
    refine mem_iUnion.mpr ⟨⟨u,hu⟩,?_⟩
    have h1 := (hone ⟨u,hu⟩).self_of_nhds
    change 0 < b ⟨u,hu⟩ (doubleCenteredWrap u u)
    rw [doubleCenteredWrap_self,h1]
    norm_num
  obtain ⟨S,hS⟩ := hK.elim_finite_subcover
    (fun c : K => {u | 0 < doublePeriodicizeBump (c:DoubleAngularVector N) (b c) u})
    (fun c => isOpen_lt continuous_const (hper c).continuous) hcover
  refine ⟨S,b,?_,?_⟩
  · intro c
    refine ⟨hb c,hcomp c,hnonneg c,?_,hsmall c⟩
    intro u hu
    have hd : dist u (c:DoubleAngularVector N) < min (radius c) (1/4) := hsupp c hu
    change dist u (c:DoubleAngularVector N) ≤ radius c
    exact (le_of_lt hd).trans (min_le_left _ _)
  · intro u hu
    obtain ⟨c,hc,hpos⟩ := mem_iUnion₂.mp (hS hu)
    have hsum := Finset.single_le_sum (s := S)
      (fun c _ => (hnonneg c (doubleCenteredWrap (c:DoubleAngularVector N) u)).1) hc
    exact hpos.trans_le hsum

end
end IsingBulk.First
