import IsingBulk.First.IntegratedMeanDecomposition
import IsingBulk.First.ActualLocalizedPostMeanAsymptotic

/-! The actual local smooth mean-and-shape integral has the source nonzero
leading asymptotic, with all source-s derivatives taken at a fixed evaluation
radius and all mean-side and shape-remainder estimates instantiated. -/
namespace IsingBulk.First
noncomputable section
open IsingBulk.Branch Complex Filter
open scoped Topology

theorem actual_local_mean_source_asymptotic {n : ℕ} (hn : 1 ≤ n)
    (a : OrderedChartData) (he : Even (n+1))
    (ha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I)=1)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I)=1) :
    let k := (n+1)^2/2-1
    localLeadingCoefficient a n k ≠ 0 ∧
    ∃ D : ℝ, 0 < D ∧ ∀ delta : ℝ, 0 < delta → delta ≤ D →
      ∃ R : ℝ, 0 < R ∧ ∀ eta : ℝ → ℂ, Continuous eta →
        (∀ v : ℝ, |v| ≤ delta → eta v=1) →
        ∀ chi : ShapeSpace n → ℂ, Continuous chi → chi 0=1 → (∀ x, ‖chi x‖ ≤ 1) →
          (∀ x, chi x ≠ 0 → ‖x‖ < R) →
          Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
            (fun epsilon => (deriv^[k] (localizedSmoothMeanIntegral a chi eta
              (-(Real.sin a.theta/4)*epsilon) delta)) (radialParameter a.theta epsilon)-
              ((Real.sqrt epsilon:ℂ)⁻¹)*localLeadingCoefficient a n k)
            (fun epsilon => (Real.sqrt epsilon:ℂ)⁻¹) := by
  dsimp only
  obtain ⟨hL,Rp,hRp,hP⟩ := actual_localized_postMean_source_asymptotic hn a he ha hb
  refine ⟨hL,?_⟩
  obtain ⟨Dd,hDd,hD⟩ := actual_integrated_mean_derivative_decomposition (n := n) a ha hb
  obtain ⟨De,hDe,hE⟩ := actual_mean_error_shape_sqrt_limit (n := n) a ha hb
  refine ⟨min Dd De,lt_min hDd hDe,?_⟩
  intro delta hd hdD
  obtain ⟨Rd,epsilon₀,hRd,he0,hDec⟩ := hD delta hd (hdD.trans (min_le_left _ _))
  obtain ⟨Re,hRe,hErr⟩ := hE delta hd (hdD.trans (min_le_right _ _))
  let R := min Rp (min Rd Re)
  have hR : 0 < R := lt_min hRp (lt_min hRd hRe)
  have hRRp : R ≤ Rp := min_le_left _ _
  have hRRd : R ≤ Rd := (min_le_right _ _).trans (min_le_left _ _)
  have hRRe : R ≤ Re := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨R,hR,?_⟩
  intro eta heta heta1 chi hchi hchi0 hchib hchis
  have hPost := hP chi hchi hchi0 hchib (fun x hx => (hchis x hx).trans_le hRRp)
  have hError := normalized_sqrt_limit_isLittleO
    (hErr eta heta chi hchi hchib (fun x hx => (hchis x hx).trans_le hRRe) ((n+1)^2/2-1))
  simp only [mul_zero,sub_zero] at hError
  apply (hPost.add hError).congr' ?_ (Eventually.of_forall (fun _ => rfl))
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds he0).filter_mono nhdsWithin_le_nhds] with epsilon he he0'
  rw [hDec eta heta heta1 chi hchi (fun x hx => (hchis x hx).trans_le hRRd) epsilon he he0']
  ring

end
end IsingBulk.First
