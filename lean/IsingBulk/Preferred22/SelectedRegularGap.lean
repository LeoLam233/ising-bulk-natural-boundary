import IsingBulk.Preferred22.SelectedBranchDisk
import IsingBulk.Preferred22.BalancedPairGeometry

/-! A genuine particle-independent discriminant margin for all coordinates
outside the two true-branch plateaux. The smooth cutoffs remain real. -/
namespace IsingBulk.Preferred22
noncomputable section
open Filter Set
open scoped Topology
set_option maxHeartbeats 1000000

def preferredSelectedRegularAngles (d : PreferredBranchData) (B : PreferredCoareaBump d) : Set ℝ :=
  Icc (-Real.pi) Real.pi ∩ {θ : ℝ | |θ|≤B.delta ∨ Real.pi-B.delta≤|θ|}

lemma preferred_selected_nonplateau_regular {d : PreferredBranchData}
    (B : PreferredCoareaBump d) {θ : ℝ} (hθ : θ∈Icc (-Real.pi) Real.pi)
    (hp : B.p θ≠1) (hm : B.m θ≠1) : θ∈preferredSelectedRegularAngles d B := by
  refine ⟨hθ,?_⟩
  change |θ|≤B.delta ∨ Real.pi-B.delta≤|θ|
  by_contra! h
  by_cases ht : 0≤θ
  · rw [abs_of_nonneg ht] at h
    exact hp (B.plateau θ ⟨h.1.le,h.2.le⟩)
  · rw [abs_of_neg (lt_of_not_ge ht)] at h
    exact hm (B.plateau (-θ) ⟨h.1.le,h.2.le⟩)

lemma preferred_selected_regular_compact (d : PreferredBranchData) (B : PreferredCoareaBump d) :
    IsCompact (preferredSelectedRegularAngles d B) := by
  apply isCompact_Icc.inter_right
  exact (isClosed_le continuous_abs continuous_const).union
    (isClosed_le continuous_const continuous_abs)

/-- At the unit-circle center, every non-plateau coordinate stays uniformly
away from both dispersion branch points. The margin is derived from the
actual canonical plateau inequalities. -/
theorem preferred_selected_regular_reference_gap (d : PreferredBranchData)
    (B : PreferredCoareaBump d) :
    ∃ γ : ℝ, 0<γ ∧ ∀ θ∈preferredSelectedRegularAngles d B,
      γ≤‖(preferredRadialTrace d 0-Complex.cos (θ:ℂ))^2-1‖ := by
  let g := min (Real.cos B.delta-Real.cos d.b)
    (Real.cos d.b-Real.cos (Real.pi-B.delta))
  have hδb : B.delta<d.b := by linarith [B.delta_b,d.b_pos]
  have hδπ : B.delta<Real.pi := hδb.trans d.b_lt
  have hg1 : 0<Real.cos B.delta-Real.cos d.b := sub_pos.mpr
    (Real.cos_lt_cos_of_nonneg_of_le_pi B.delta_pos.le d.b_lt.le hδb)
  have hg2 : 0<Real.cos d.b-Real.cos (Real.pi-B.delta) := sub_pos.mpr
    (Real.cos_lt_cos_of_nonneg_of_le_pi d.b_pos.le (by linarith [B.delta_pos]) B.branch_plateau)
  have hg : 0<g := lt_min hg1 hg2
  have hc : 0<1+Real.cos d.b := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi d.b_pos.le (le_refl Real.pi) d.b_lt
    rw [Real.cos_pi] at h
    linarith
  refine ⟨g*(1+Real.cos d.b),mul_pos hg hc,?_⟩
  intro θ hθ
  have habs : |θ|≤Real.pi := abs_le.mpr hθ.1
  have hcos : Real.cos |θ|=Real.cos θ := Real.cos_abs θ
  have hsmall : g≤|Real.cos d.b-Real.cos θ| := by
    rcases hθ.2 with hlo|hhi
    · have hm := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg θ) hδπ.le hlo
      rw [hcos] at hm
      have hle : Real.cos d.b-Real.cos θ≤0 := by linarith
      rw [abs_of_nonpos hle]
      have hmin := min_le_left (Real.cos B.delta-Real.cos d.b)
        (Real.cos d.b-Real.cos (Real.pi-B.delta))
      dsimp only [g]
      linarith
    · have hm := Real.cos_le_cos_of_nonneg_of_le_pi (by linarith : 0≤Real.pi-B.delta) habs hhi
      rw [hcos] at hm
      have hle : 0≤Real.cos d.b-Real.cos θ := by linarith
      rw [abs_of_nonneg hle]
      have hmin := min_le_right (Real.cos B.delta-Real.cos d.b)
        (Real.cos d.b-Real.cos (Real.pi-B.delta))
      dsimp only [g]
      linarith
  have hlarge : 1+Real.cos d.b≤|2+Real.cos d.b-Real.cos θ| := by
    have h := Real.cos_le_one θ
    exact (by linarith : 1+Real.cos d.b≤2+Real.cos d.b-Real.cos θ).trans (le_abs_self _)
  have he : (preferredRadialTrace d 0-Complex.cos (θ:ℂ))^2-1 =
      ((Real.cos d.b-Real.cos θ:ℝ):ℂ)*((2+Real.cos d.b-Real.cos θ:ℝ):ℂ) := by
    rw [preferredRadialTrace_zero,←Complex.ofReal_cos]
    push_cast
    ring
  rw [he,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs]
  exact mul_le_mul hsmall hlarge hc.le (abs_nonneg _)

/-- The regular-coordinate margin persists for the actual deformed angle,
uniformly in both independent occupancy fractions before particle count. -/
theorem preferred_selected_regular_source_gap (d : PreferredBranchData)
    (B : PreferredCoareaBump d) :
    ∃ γ ρ : ℝ,0<γ ∧ 0<ρ ∧ ∀ ε τ σ υ θ : ℝ,
      |ε|<ρ → |τ|<ρ → σ∈Icc 0 1 → υ∈Icc 0 1 →
      θ∈preferredSelectedRegularAngles d B →
      γ≤‖(preferredRadialTrace d ε-Complex.cos
        (preferredBumpAngle B.m B.p τ σ υ θ))^2-1‖ := by
  obtain ⟨γ,hγ,hbase⟩ := preferred_selected_regular_reference_gap d B
  let K : Set (ℝ × ℝ × ℝ) := preferredSelectedRegularAngles d B ×ˢ (Icc 0 1 ×ˢ Icc 0 1)
  have hK : IsCompact K := (preferred_selected_regular_compact d B).prod
    (isCompact_Icc.prod isCompact_Icc)
  let F : (ℝ × ℝ) → (ℝ × ℝ × ℝ) → ℝ := fun x y =>
    ‖(preferredRadialTrace d x.1-Complex.cos
      (preferredBumpAngle B.m B.p x.2 y.2.1 y.2.2 y.1))^2-1‖
  have hcont (y : ℝ × ℝ × ℝ) :
      ContinuousAt (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) => F z.1 z.2) ((0,0),y) := by
    have hp : Continuous B.p := B.smooth.continuous
    have hm : Continuous B.m := hp.comp continuous_neg
    unfold F preferredBumpAngle preferredRadialTrace IsingBulk.Branch.radialParameter
    fun_prop (disch := simp)
  have hevent : ∀ᶠ x in 𝓝 ((0,0):ℝ × ℝ),∀ y∈K,γ/2<F x y := by
    apply hK.eventually_forall_of_forall_eventually
    intro y hy
    have hzero : F (0,0) y=‖(preferredRadialTrace d 0-Complex.cos (y.1:ℂ))^2-1‖ := by
      simp [F,preferredBumpAngle]
    have hb : γ/2<F (0,0) y := by rw [hzero]; linarith [hbase y.1 hy.1]
    exact continuousAt_const.eventually_lt (hcont y) hb
  obtain ⟨ρ,hρ,hball⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨γ/2,ρ,by positivity,hρ,?_⟩
  intro ε τ σ υ θ hε hτ hσ hυ hθ
  have hdist : dist (ε,τ) ((0,0):ℝ × ℝ)<ρ := by
    change dist (ε,τ) (0:ℝ × ℝ)<ρ
    simpa only [dist_zero_right,Prod.norm_def,Real.norm_eq_abs,max_lt_iff] using And.intro hε hτ
  exact (hball hdist (θ,σ,υ) ⟨hθ,hσ,hυ⟩).le

end
end IsingBulk.Preferred22
