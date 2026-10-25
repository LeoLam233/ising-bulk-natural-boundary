import IsingBulk.Joint.Negative.FamilyGapControl
import IsingBulk.Joint.Negative.FamilyAnalyticControl

namespace IsingBulk.Joint.Negative
noncomputable section
open IsingBulk.Tail IsingBulk.Anisotropic.RegularEdges
  IsingBulk.Anisotropic.NegativeDominance IsingBulk.Joint.RegularEdges Set Metric
open scoped Topology BigOperators

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Common a/N Cauchy bounds after actual joint holomorphic substitution.
The boundary gap is a geometric intermediate condition, later discharged by
uniform outer or selected-phase nonresonant root estimates. -/
theorem compact_family_integrand_cauchy_of_boundary_gap {b : ℝ} {Q : Set E}
    (H : ℂ × E→NumeratorParameter) (hb : |b|<1) (hQ : IsCompact Q)
    (hH : ∀eta∈Q, AnalyticAt ℂ H (0,eta)) (hzero : ∀eta∈Q, (H (0,eta)).1=0)
    (hB : ∀eta∈Q, 0<(H (0,eta)).2.1.im) (hS : ∀eta∈Q, (H (0,eta)).2.2≠0)
    (κ : ℝ) (hκ : 0<κ) :
    ∃a r C M K : ℝ,0<a ∧ 0<r ∧ r<1 ∧ 0<C ∧ 0<M ∧ 0<K ∧
      ∀eta∈Q, ∀j N : ℕ,1≤N → ∀q : Fin N→ℝ,
      (∀i,q i∈Icc (-Real.pi) Real.pi) → κ≤‖1-∏i,edgeRoot b (H (0,eta)).2.1 (q i)‖ →
      ‖iteratedDeriv j (fun t=>independentFullIntegrand b (H (t,eta)) q) 0‖≤
        (j.factorial:ℝ)*(K*particleEdgeMajorant r C M N)/(a/(N:ℝ))^j := by
  have hc : ContinuousOn (fun eta => (H (0,eta)).2) Q := by
    intro eta heta
    exact ((hH eta heta).continuousAt.comp
      (continuous_const.prodMk continuous_id).continuousAt).snd.continuousWithinAt
  obtain ⟨a,r,C,M,K,ha,hr,hr1,hC,hM,hK,hcontrol⟩ :=
    compact_full_integrand_disk_of_boundary_gap hb (hQ.image_of_continuousOn hc)
      (by rintro w ⟨eta,heta,rfl⟩; exact hB eta heta)
      (by rintro w ⟨eta,heta,rfl⟩; exact hS eta heta) κ hκ
  obtain ⟨δ,L,hδ,hL,hlin⟩ := compact_family_analytic_linear_bound H hQ hH
  let A := min δ (a/L)
  have hA : 0<A := lt_min hδ (div_pos ha hL)
  have hcontrol' : ∀eta∈Q, ∀N : ℕ,1≤N → ∀q : Fin N→ℝ,
      (∀i,q i∈Icc (-Real.pi) Real.pi) → κ≤‖1-∏i,edgeRoot b (H (0,eta)).2.1 (q i)‖ →
      ∀u : ℂ, ‖u‖<A/(N:ℝ) →
      AnalyticAt ℂ (fun t=>independentFullIntegrand b (H (t,eta)) q) u ∧
      ‖independentFullIntegrand b (H (u,eta)) q‖≤K*particleEdgeMajorant r C M N := by
    intro eta heta N hN q hq hgap u hu
    have hNR : (1:ℝ)≤N := by exact_mod_cast hN
    have hNp : (0:ℝ)<N := by linarith
    have hsmall : A/(N:ℝ)≤A := (div_le_iff₀ hNp).mpr (by nlinarith)
    have huδ : ‖u‖<δ := hu.trans_le (hsmall.trans (min_le_left _ _))
    obtain ⟨hHu,hHn⟩ := hlin eta heta u huδ
    have hHe : H (0,eta)=((0:ℂ),(H (0,eta)).2) := Prod.ext (hzero eta heta) rfl
    have hball : H (u,eta)∈ball ((0:ℂ),(H (0,eta)).2) (a/(N:ℝ)) := by
      rw [mem_ball,dist_eq_norm,←hHe]
      calc
        ‖H (u,eta)-H (0,eta)‖ ≤ L*‖u‖ := hHn
        _ < L*(A/(N:ℝ)) := mul_lt_mul_of_pos_left hu hL
        _ ≤ L*((a/L)/(N:ℝ)) := mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right (min_le_right _ _) hNp.le) hL.le
        _ = a/(N:ℝ) := by field_simp
    have hh := hcontrol (H (0,eta)).2 (mem_image_of_mem _ heta) N hN q hq hgap _ hball
    exact ⟨hh.1.comp (f := fun t => H (t,eta)) hHu,hh.2⟩
  refine ⟨A/2,r,C,M,K,half_pos hA,hr,hr1,hC,hM,hK,?_⟩
  intro eta heta j N hN q hq hgap
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  let R : ℝ := (A/2)/(N:ℝ)
  have hR : 0<R := by dsimp [R]; positivity
  have hsub : closedBall (0:ℂ) R⊆ball 0 (A/(N:ℝ)) := by
    intro u hu
    have hh : ‖u‖≤R := by simpa using hu
    have hhalf : R<A/(N:ℝ) := by dsimp [R]; exact div_lt_div_of_pos_right (half_lt_self hA) hNp
    simpa using hh.trans_lt hhalf
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j hR
  · apply DifferentiableOn.diffContOnCl_ball (U := ball 0 (A/(N:ℝ))) _ hsub
    intro u hu
    exact (hcontrol' eta heta N hN q hq hgap u (by simpa using hu)).1.differentiableAt.differentiableWithinAt
  · intro u hu
    exact (hcontrol' eta heta N hN q hq hgap u (by simpa using hsub (sphere_subset_closedBall hu))).2

end
end IsingBulk.Joint.Negative
