import IsingBulk.Joint.RegularEdges.FamilyLeadingDominated

namespace IsingBulk.Joint.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Anisotropic.RegularEdges MeasureTheory Set Filter Metric
open scoped Topology

theorem filtered_edge_shape_cutoff_limit {α : Type*} {l : Filter α}
    [l.IsCountablyGenerated] {τ : α → ℝ} (hτ : Tendsto τ l (𝓝[>] 0)) {n k a : ℕ}
    (hbalance : n+a+(n+1)*n=2*(k+1))
    (hmajorant : Integrable (@shapeMajorant n k)) (A D : α → ShapeSpace n → ℂ)
    (chi : ShapeSpace n → ℂ) (a₀ : ℂ) {R Q M c : ℝ} {w : ℂ}
    (hR : 0 < R) (hQ : 0 < Q) (hw : 0 < w.re) (hM : 0 ≤ M) (hc : 0 < c)
    (hchi : Continuous chi) (hchi0 : chi 0 = 1)
    (hchib : ∀ x, ‖chi x‖ ≤ 1) (hchis : ∀ x, chi x ≠ 0 → ‖x‖ < R)
    (hregular : ∀ᶠ lam in l, ContinuousOn (A lam) (ball 0 R) ∧
      ContinuousOn (D lam) (ball 0 R) ∧
      (∀ x ∈ ball 0 R, ‖A lam x‖ ≤ M) ∧
      (∀ x ∈ ball 0 R, c*((τ lam)^2+‖x‖^2) ≤ ‖D lam x‖))
    (hAlimit : ∀ x, Tendsto (fun lam => A lam (τ lam • x)) l (𝓝 a₀))
    (hDlimit : ∀ x, Tendsto (fun lam => D lam (τ lam • x)/(τ lam:ℂ)^2)
      l (𝓝 ((Q:ℂ)+w*(‖x‖:ℂ)^2))) :
    Tendsto (fun lam => ((τ lam)^a) • ∫ x : ShapeSpace n,
      (shapeVandermondeSq x:ℂ)*chi x*A lam x/(D lam x)^(k+1))
      l (𝓝 (a₀*shapePeriodIntrinsic n k Q w)) := by
  classical
  let AA : α → ShapeSpace n → ℂ := fun lam =>
    (ball 0 R).piecewise (fun x => chi x*A lam x) (fun _ => 0)
  let DD : α → ShapeSpace n → ℂ := fun lam =>
    (ball 0 R).piecewise (D lam) (fun _ => 1)
  have hreg : ∀ᶠ lam in l, Measurable (AA lam) ∧ Measurable (DD lam) ∧
      (∀ x, ‖AA lam x‖ ≤ M) ∧
      (∀ x, AA lam x ≠ 0 → c*((τ lam)^2+‖x‖^2) ≤ ‖DD lam x‖) := by
    filter_upwards [hregular] with lam hlam
    refine ⟨(hchi.continuousOn.mul hlam.1).measurable_piecewise
      continuous_const.continuousOn measurableSet_ball,
      hlam.2.1.measurable_piecewise continuous_const.continuousOn measurableSet_ball, ?_, ?_⟩
    · intro x
      by_cases hx : x ∈ ball 0 R
      · simp only [AA, piecewise_eq_of_mem _ _ _ hx, norm_mul]
        calc
          ‖chi x‖*‖A lam x‖ ≤ 1*M := mul_le_mul (hchib x) (hlam.2.2.1 x hx)
            (norm_nonneg _) zero_le_one
          _ = M := one_mul _
      · simpa only [AA, piecewise_eq_of_notMem _ _ _ hx, norm_zero] using hM
    · intro x hx
      have hmem : x ∈ ball 0 R := by
        by_contra hh
        exact hx (piecewise_eq_of_notMem _ _ _ hh)
      simpa only [DD, piecewise_eq_of_mem _ _ _ hmem] using hlam.2.2.2 x hmem
  have hxevent (x : ShapeSpace n) : ∀ᶠ lam : α in l, τ lam • x ∈ ball 0 R := by
    have ht : Tendsto (fun lam : α => τ lam • x) l (𝓝 0) := by
      simpa using! (hτ.mono_right nhdsWithin_le_nhds).smul_const x
    exact ht.eventually (ball_mem_nhds 0 hR)
  have hAl (x : ShapeSpace n) : Tendsto (fun lam => AA lam (τ lam • x)) l (𝓝 a₀) := by
    have ht : Tendsto (fun lam : α => τ lam • x) l (𝓝 0) := by
      simpa using! (hτ.mono_right nhdsWithin_le_nhds).smul_const x
    have hh := (hchi.continuousAt.tendsto.comp ht).mul (hAlimit x)
    rw [hchi0, one_mul] at hh
    apply hh.congr'
    filter_upwards [hxevent x] with lam hlam
    simp only [Function.comp_apply, AA, piecewise_eq_of_mem _ _ _ hlam]
  have hDl (x : ShapeSpace n) : Tendsto (fun lam => DD lam (τ lam • x)/(τ lam:ℂ)^2)
      l (𝓝 ((Q:ℂ)+w*(‖x‖:ℂ)^2)) := by
    apply (hDlimit x).congr'
    filter_upwards [hxevent x] with lam hlam
    simp only [DD, piecewise_eq_of_mem _ _ _ hlam]
  have h := filtered_edge_shape_dominated_limit hτ hbalance hmajorant AA DD a₀ hQ hw hM hc
    hreg hAl hDl
  apply h.congr'
  exact Eventually.of_forall fun lam => by
    dsimp only
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      by_cases hx : x ∈ ball 0 R
      · simp only [localShapeQuotient, AA, DD, piecewise_eq_of_mem _ _ _ hx]
        ring
      · have hz : chi x = 0 := by
          by_contra hh
          exact hx (by simpa only [mem_ball, dist_zero_right] using hchis x hh)
        simp only [localShapeQuotient, AA, DD, piecewise_eq_of_notMem _ _ _ hx, hz,
          mul_zero, zero_mul, zero_div]


end
end IsingBulk.Joint.RegularEdges
