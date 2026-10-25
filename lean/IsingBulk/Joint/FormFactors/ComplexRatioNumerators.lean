import IsingBulk.Joint.FormFactors.ComplexRatioBounds
import IsingBulk.Joint.RegularEdges.CompactMixedJets

/-! Actual complex-ratio substitution in the complete numerator estimates.
Cauchy is applied AFTER composing with the true varying-ratio family, so the
bounds include mixed edge-parameter/lambda derivatives, not just frozen-B jets. -/
namespace IsingBulk.Joint.FormFactors
noncomputable section
open Set Filter Metric
open scoped Topology
open IsingBulk.Anisotropic.RegularEdges

variable {b : ℝ} {amp : Coupling → ℂ} {z₀ lam₀ : ℂ}

def actualRatioNumerator
    (F : ComplexRatioFamily (Transverse.positiveParameter (b:ℂ)) amp 1 z₀ lam₀)
    (qs : List ℝ) (q : Coupling) : ℂ :=
  RegularEdges.independentNumerator b (q.1,(F.anisotropy q,F.scale q)) qs

/-- One common parameter disk and a summable all-particle envelope for EVERY
fixed mixed jet of the actual complex-ratio complete numerator. -/
theorem actual_complex_ratio_numerator_summable_mixed_jets (hb : |b|<1)
    (F : ComplexRatioFamily (Transverse.positiveParameter (b:ℂ)) amp 1 z₀ lam₀) :
    ∃ δ : ℝ, 0<δ ∧ ∃ G : ℕ → ℕ → ℝ,
      (∀ k, Summable (G k)) ∧ (∀ k N, 0≤G k N) ∧
      ∀ (N k : ℕ) (angles : Fin N → ℝ),
      (∀ i, angles i∈Icc (-Real.pi) Real.pi) → ∀ q∈ball (0,lam₀) δ,
      ‖iteratedFDeriv ℂ k (actualRatioNumerator F (List.ofFn angles)) q‖≤G k N := by
  obtain ⟨δ,r,C,M,hδ,hr,hr1,hC,hM,hall⟩ := RegularEdges.compact_full_numerator_polydisks
    hb F.parameterSet_isCompact
    (fun v hv => by simpa using F.parameterSet_sign hv)
    (fun _ hv => F.parameterSet_scale_ne_zero hv)
  let R := min F.radius δ
  have hR : 0<R := lt_min F.radius_pos hδ
  have hparam (q : Coupling) (hq : q∈ball (0,lam₀) R) :
      q∈F.polydisk ∧
      (q.1,(F.anisotropy q,F.scale q))∈ball ((0:ℂ),(F.anisotropy q,F.scale q)) δ := by
    have hh : ‖q.1‖<R ∧ dist q.2 lam₀<R := by
      simpa only [mem_ball,Prod.dist_eq,dist_zero_right,max_lt_iff] using hq
    constructor
    · exact ⟨by simpa only [mem_closedBall,dist_zero_right] using hh.1.le.trans (min_le_left F.radius δ),
        hh.2.le.trans (min_le_left _ _)⟩
    · simp only [mem_ball,Prod.dist_eq,dist_self,max_lt_iff,dist_zero_right]
      exact ⟨hh.1.trans_le (min_le_right _ _),hδ⟩
  have hfull (N : ℕ) (angles : Fin N → ℝ)
      (hang : ∀ i, angles i∈Icc (-Real.pi) Real.pi) :
      AnalyticOnNhd ℂ (actualRatioNumerator F (List.ofFn angles)) (ball (0,lam₀) R) ∧
      ∀ q∈ball (0,lam₀) R, ‖actualRatioNumerator F (List.ofFn angles) q‖≤
        particleEdgeMajorant r C M N := by
    constructor
    · intro q hq
      have hd := hparam q hq
      have hv : (F.anisotropy q,F.scale q)∈F.parameterSet := ⟨q,hd.1,rfl⟩
      exact ((hall _ hv N angles hang).1 _ hd.2).comp
        (f := fun q : Coupling => (q.1,(F.anisotropy q,F.scale q)))
        (analyticAt_fst.prod ((F.anisotropy_analyticOnNhd q hd.1).prod (F.scale_analyticOnNhd q hd.1)))
    · intro q hq
      have hd := hparam q hq
      exact (hall _ (show (F.anisotropy q,F.scale q)∈F.parameterSet from ⟨q,hd.1,rfl⟩)
        N angles hang).2 _ hd.2
  refine ⟨R/2,half_pos hR,fun k N => particleEdgeMajorant r C M N/(R/(2*((k+1:ℕ):ℝ)))^k,?_,?_,?_⟩
  · intro k
    have hs : Summable (fun N => particleEdgeMajorant r C M N) := by
      simpa only [pow_zero,one_mul] using particleEdgeMajorant_polynomial_summable hr hr1 hC hM 0
    exact hs.div_const _
  · intro k N
    exact div_nonneg (particleEdgeMajorant_nonneg hr.le hC.le hM.le N) (by positivity)
  · intro N k angles hang q hq
    exact RegularEdges.norm_iteratedFDeriv_le_on_half_ball k hR
      (particleEdgeMajorant_nonneg hr.le hC.le hM.le N) (hfull N angles hang).1
      (hfull N angles hang).2 hq

end
end IsingBulk.Joint.FormFactors
