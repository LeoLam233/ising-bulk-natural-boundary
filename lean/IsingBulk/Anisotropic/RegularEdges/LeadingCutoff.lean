import IsingBulk.Anisotropic.RegularEdges.LeadingDominated

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First MeasureTheory Set Filter Metric
open scoped Topology

theorem edge_shape_cutoff_limit {n k a : ℕ}
    (hbalance : n+a+(n+1)*n=2*(k+1))
    (hmajorant : Integrable (@shapeMajorant n k)) (A D : ℝ → ShapeSpace n → ℂ)
    (chi : ShapeSpace n → ℂ) (a₀ : ℂ) {R Q M c lam₀ : ℝ} {w : ℂ}
    (hR : 0 < R) (hQ : 0 < Q) (hw : 0 < w.re) (hM : 0 ≤ M) (hc : 0 < c)
    (hlam₀ : 0 < lam₀) (hchi : Continuous chi) (hchi0 : chi 0 = 1)
    (hchib : ∀ x, ‖chi x‖ ≤ 1) (hchis : ∀ x, chi x ≠ 0 → ‖x‖ < R)
    (hAcont : ∀ lam ∈ Ioo 0 lam₀, ContinuousOn (A lam) (ball 0 R))
    (hDcont : ∀ lam ∈ Ioo 0 lam₀, ContinuousOn (D lam) (ball 0 R))
    (hAbound : ∀ lam ∈ Ioo 0 lam₀, ∀ x ∈ ball 0 R, ‖A lam x‖ ≤ M)
    (hDbound : ∀ lam ∈ Ioo 0 lam₀, ∀ x ∈ ball 0 R,
      c*(lam^2+‖x‖^2) ≤ ‖D lam x‖)
    (hAlimit : ∀ x, Tendsto (fun lam => A lam (lam • x)) (𝓝[>] 0) (𝓝 a₀))
    (hDlimit : ∀ x, Tendsto (fun lam => D lam (lam • x)/(lam:ℂ)^2)
      (𝓝[>] 0) (𝓝 ((Q:ℂ)+w*(‖x‖:ℂ)^2))) :
    Tendsto (fun lam => (lam^a) • ∫ x : ShapeSpace n,
      (shapeVandermondeSq x:ℂ)*chi x*A lam x/(D lam x)^(k+1))
      (𝓝[>] 0) (𝓝 (a₀*shapePeriodIntrinsic n k Q w)) := by
  classical
  let AA : ℝ → ShapeSpace n → ℂ := fun lam =>
    (ball 0 R).piecewise (fun x => chi x*A lam x) (fun _ => 0)
  let DD : ℝ → ShapeSpace n → ℂ := fun lam =>
    (ball 0 R).piecewise (D lam) (fun _ => 1)
  have hAm (lam : ℝ) (hlam : lam ∈ Ioo 0 lam₀) : Measurable (AA lam) :=
    (hchi.continuousOn.mul (hAcont lam hlam)).measurable_piecewise
      continuous_const.continuousOn measurableSet_ball
  have hDm (lam : ℝ) (hlam : lam ∈ Ioo 0 lam₀) : Measurable (DD lam) :=
    (hDcont lam hlam).measurable_piecewise continuous_const.continuousOn measurableSet_ball
  have hAb (lam : ℝ) (hlam : lam ∈ Ioo 0 lam₀) (x : ShapeSpace n) : ‖AA lam x‖ ≤ M := by
    by_cases hx : x ∈ ball 0 R
    · simp only [AA, piecewise_eq_of_mem _ _ _ hx, norm_mul]
      calc
        ‖chi x‖*‖A lam x‖ ≤ 1*M := mul_le_mul (hchib x) (hAbound lam hlam x hx)
          (norm_nonneg _) (by positivity)
        _ = M := one_mul _
    · simpa only [AA, piecewise_eq_of_notMem _ _ _ hx, norm_zero] using hM
  have hDb (lam : ℝ) (hlam : lam ∈ Ioo 0 lam₀) (x : ShapeSpace n)
      (hx : AA lam x ≠ 0) : c*(lam^2+‖x‖^2) ≤ ‖DD lam x‖ := by
    have hmem : x ∈ ball 0 R := by
      by_contra hh
      exact hx (piecewise_eq_of_notMem _ _ _ hh)
    simpa only [DD, piecewise_eq_of_mem _ _ _ hmem] using hDbound lam hlam x hmem
  have hxevent (x : ShapeSpace n) : ∀ᶠ lam : ℝ in 𝓝[>] 0, lam • x ∈ ball 0 R := by
    have ht : Tendsto (fun lam : ℝ => lam • x) (𝓝[>] 0) (𝓝 0) := by
      simpa using! ((continuous_id.smul (continuous_const : Continuous (fun _ : ℝ => x))).tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
    exact ht.eventually (ball_mem_nhds 0 hR)
  have hAl (x : ShapeSpace n) : Tendsto (fun lam => AA lam (lam • x)) (𝓝[>] 0) (𝓝 a₀) := by
    have ht : Tendsto (fun lam : ℝ => lam • x) (𝓝[>] 0) (𝓝 0) := by
      simpa using! ((continuous_id.smul (continuous_const : Continuous (fun _ : ℝ => x))).tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
    have hh := (hchi.continuousAt.tendsto.comp ht).mul (hAlimit x)
    rw [hchi0, one_mul] at hh
    apply hh.congr'
    filter_upwards [hxevent x] with lam hlam
    simp only [Function.comp_apply, AA, piecewise_eq_of_mem _ _ _ hlam]
  have hDl (x : ShapeSpace n) : Tendsto (fun lam => DD lam (lam • x)/(lam:ℂ)^2)
      (𝓝[>] 0) (𝓝 ((Q:ℂ)+w*(‖x‖:ℂ)^2)) := by
    apply (hDlimit x).congr'
    filter_upwards [hxevent x] with lam hlam
    simp only [DD, piecewise_eq_of_mem _ _ _ hlam]
  have h := edge_shape_dominated_limit hbalance hmajorant AA DD a₀ hQ hw hM hc hlam₀
    hAm hDm hAb hDb hAl hDl
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
end IsingBulk.Anisotropic.RegularEdges
