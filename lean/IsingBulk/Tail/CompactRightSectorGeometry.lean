import IsingBulk.Tail.ConstructedSectorPartition
import IsingBulk.Tail.CompactRightCurvature
import IsingBulk.Tail.ProtectedAngularWrap

/-! The actual right-sector support provides a fixed curvature margin and
one convex signed interval. All finite cutoff jets inherit that same margin. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set
open scoped Topology

def rightSectorRadius (b δ : ℝ) : ℝ := Real.arccos (Real.cos b+δ/2)

theorem right_sector_phase_margin {b δ θ : ℝ} (hb : 0<b) (hbπ : b<Real.pi) (_hδ : 0<δ)
    (hθ : sectorDisplacement b θ≤ -δ/2) :
    |1+Real.cos b-Real.cos θ|≤1-min (δ/2) ((1+Real.cos b)/2) := by
  have hbcos : -1<Real.cos b := by
    have hh := Real.strictAntiOn_cos ⟨hb.le,hbπ.le⟩ ⟨Real.pi_pos.le,le_rfl⟩ hbπ
    simpa only [Real.cos_pi] using hh
  have hd : min (δ/2) ((1+Real.cos b)/2)≤δ/2 := min_le_left _ _
  have hc : min (δ/2) ((1+Real.cos b)/2)≤(1+Real.cos b)/2 := min_le_right _ _
  rw [abs_le]
  unfold sectorDisplacement at hθ
  constructor <;> linarith [Real.cos_le_one θ]

theorem right_sector_jet_curvature (d : LocalBranchData) {δ : ℝ} (hδ : 0<δ) (j : ℕ)
    {θ : ℝ} (hθ : θ ∈ tsupport (iteratedFDeriv ℝ j (sectorRight d.thetaB δ hδ))) :
    deriv (deriv (compactRightPhase (1+Real.cos d.thetaB))) θ≤
      -(1+Real.cos d.thetaB)*min (δ/2) ((1+Real.cos d.thetaB)/2) := by
  have hS : 0<1+Real.cos d.thetaB := by
    have hh := Real.strictAntiOn_cos ⟨d.thetaB_pos.le,d.thetaB_lt.le⟩ ⟨Real.pi_pos.le,le_rfl⟩ d.thetaB_lt
    simp only [Real.cos_pi] at hh
    linarith
  exact compactRightPhase_uniform_curvature hS (lt_min (half_pos hδ) (half_pos hS)) θ
    (right_sector_phase_margin d.thetaB_pos d.thetaB_lt hδ
      ((sector_label_finite_jets_support d.thetaB δ hδ j).2.1 hθ))

theorem right_sector_signed_interval {b δ θ : ℝ} (hθπ : |θ|≤Real.pi)
    (hθ : sectorDisplacement b θ≤ -δ/2) : |θ|≤rightSectorRadius b δ := by
  have hc : Real.cos b+δ/2≤Real.cos θ := by unfold sectorDisplacement at hθ; linarith
  have hh := Real.arccos_le_arccos hc
  rw [← Real.cos_abs,Real.arccos_cos (abs_nonneg _) hθπ] at hh
  exact hh

theorem right_sector_radius_bounds {b δ : ℝ} (hb : 0<b) (hbπ : b<Real.pi)
    (hδ : 0<δ) (hδsmall : δ<2*(1-Real.cos b)) :
    0<rightSectorRadius b δ ∧ rightSectorRadius b δ<b := by
  have hbcos : -1<Real.cos b := by
    have hh := Real.strictAntiOn_cos ⟨hb.le,hbπ.le⟩ ⟨Real.pi_pos.le,le_rfl⟩ hbπ
    simpa only [Real.cos_pi] using hh
  have hx0 : -1<Real.cos b+δ/2 := by linarith
  have hx1 : Real.cos b+δ/2<1 := by linarith
  constructor
  · exact Real.arccos_pos.mpr hx1
  · have hh := Real.strictAntiOn_arccos ⟨(Real.neg_one_le_cos b), (Real.cos_le_one b)⟩
      ⟨hx0.le,hx1.le⟩ (show Real.cos b<Real.cos b+δ/2 by linarith)
    rw [Real.arccos_cos hb.le hbπ.le] at hh
    exact hh

theorem right_sector_interval_uniform_margin {b δ : ℝ} (hb : 0<b) (hbπ : b<Real.pi)
    (hδ : 0<δ) (hδsmall : δ<2*(1-Real.cos b)) :
    ∀ θ ∈ Icc (-rightSectorRadius b δ) (rightSectorRadius b δ),
      |1+Real.cos b-Real.cos θ|≤1-min (δ/2) ((1+Real.cos b)/2) := by
  intro θ hθ
  obtain ⟨hr,hrb⟩ := right_sector_radius_bounds hb hbπ hδ hδsmall
  have ha : |θ|≤rightSectorRadius b δ := abs_le.mpr hθ
  have hcos := Real.antitoneOn_cos ⟨abs_nonneg θ,ha.trans (hrb.le.trans hbπ.le)⟩
    ⟨hr.le,hrb.le.trans hbπ.le⟩ ha
  have hx0 : -1≤Real.cos b+δ/2 := by linarith [Real.neg_one_le_cos b]
  have hx1 : Real.cos b+δ/2≤1 := by linarith
  rw [rightSectorRadius,Real.cos_arccos hx0 hx1,Real.cos_abs] at hcos
  exact right_sector_phase_margin hb hbπ hδ (by unfold sectorDisplacement; linarith)

end
end IsingBulk.Tail
