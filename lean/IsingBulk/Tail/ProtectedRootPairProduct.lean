import IsingBulk.Tail.ProtectedActualPairs
import IsingBulk.Tail.SelectedFRootProduct

/-! Actual current-support compact Gaussian suppression, uniform in lambda. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set
open scoped BigOperators Topology
 theorem protected_actual_root_pair_product (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ η₀ τ₀ : ℝ, 0 < η₀ ∧ 0 < τ₀ ∧
      ∀ η α τ : ℝ, 0 < η → η < η₀ → 0 < α → α < Real.sin d.thetaB/4 →
        0 < τ → τ < τ₀ → ∃ c eps₀ B a : ℝ, 0 < c ∧ 0 < eps₀ ∧ 0 < B ∧ 0 < a ∧
        ∀ (N : ℕ) (eps lamStar lam : ℝ) (θ : Fin N → ℝ) (qidx : Fin N) (s : ℂ),
          1 ≤ N → 0 < eps → eps < eps₀ → 0 < lamStar → lamStar ≤ lam → lam ≤ 1 → θ ∈ angleBox N →
          θ ∈ tsupport (namedSelectorDerivative (constructedSelector d.thetaB η α) qidx) →
          ‖s-radialParameter d.theta eps‖ ≤ c*lamStar/(N:ℝ)^2 →
          ‖First.pairProduct (fun i => selectedContinuedRoot s
            (deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ lam θ i))‖ ≤
            B^N*Real.exp (-a*((selectedCompactIndexSet d.thetaB η θ).card:ℝ)^2) := by
  obtain ⟨η₀,τ₀,hη₀,hτ₀,hpairs⟩ := protected_actual_pair_bounds d hcsmall
  refine ⟨η₀,τ₀,hη₀,hτ₀,?_⟩
  intro η α τ hη hηlt hα hαsmall hτ hτlt
  obtain ⟨c,eps₀,C,q,hc,heps₀,hC,hq,hq1,hb⟩ := hpairs η α τ hη hηlt hα hαsmall hτ hτlt
  have hlog : Real.log q < 0 := Real.log_neg hq hq1
  refine ⟨c,eps₀,Real.exp (C-Real.log q/2),-Real.log q/4,hc,heps₀,Real.exp_pos _,by linarith,?_⟩
  intro N eps lamStar lam θ qidx s hN heps hepslt hls hl hl1 hθ hsupport hsd
  obtain ⟨color,hsame,hall⟩ := hb N eps lamStar lam θ qidx s hN heps hepslt hls hl hl1 hθ hsupport hsd
  have hh := actual_pairProduct_two_group_bound (by omega : 0<N)
    (selectedCompactIndexSet d.thetaB η θ) color _ hC.le hq hq1 hsame hall
  have he : (Real.exp (C-Real.log q/2))^N=Real.exp ((C-Real.log q/2)*(N:ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he]
  simpa only [neg_div,neg_neg] using hh

end
end IsingBulk.Tail
