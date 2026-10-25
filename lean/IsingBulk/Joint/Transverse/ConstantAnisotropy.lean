import IsingBulk.Joint.Transverse.LocalSide
import IsingBulk.Joint.RegularEdges.NegativeEvenIdentity

/-! # An actual analytic constant-anisotropy transversal
This curve is constructed from the independent-coupling analytic chart. It is
used to obtain ambient obstructions from genuine curve obstructions, not in the
invalid reverse direction.
-/
namespace IsingBulk.Joint.Transverse
noncomputable section
open Set Filter
open scoped Topology

theorem exists_constant_anisotropy_curve {K : Coupling}
    (hS : S K≠0) (hp : p K^2≠1) :
    ∃ curve : ℂ → Coupling, AnalyticAt ℂ curve 0 ∧ curve 0=K ∧
      ∀ᶠ u in 𝓝 (0:ℂ), transferC (curve u)=transferC K+u ∧ transferB (curve u)=transferB K := by
  obtain ⟨e,hKs,hef,_,hea⟩ := exists_transfer_localAnalyticEquiv hS hp
  let q : ℂ → Coupling := fun u => (transferC K+u,transferB K)
  have hqa : AnalyticAt ℂ q 0 := (analyticAt_const.add analyticAt_id).prod analyticAt_const
  have hq0 : q 0=transferChart K := by simp [q,transferChart]
  let curve : ℂ → Coupling := e.symm ∘ q
  have hca : AnalyticAt ℂ curve 0 := hea.comp_of_eq hqa hq0
  have hc0 : curve 0=K := by dsimp [curve]; rw [hq0,←hef]; exact e.left_inv hKs
  refine ⟨curve,hca,hc0,?_⟩
  have ht : ∀ᶠ u in 𝓝 (0:ℂ), q u∈e.target :=
    hqa.continuousAt.preimage_mem_nhds (hq0.symm ▸ (hef ▸ e.open_target.mem_nhds (e.map_source hKs)))
  filter_upwards [ht] with u hu
  have hh : transferChart (curve u)=q u := by
    rw [←hef]
    exact e.right_inv hu
  exact ⟨congrArg Prod.fst hh,congrArg Prod.snd hh⟩

theorem exists_positive_normal_curve {K : Coupling} {b : ℝ}
    (hS : S K≠0) (hp : p K^2≠1) (he : positiveParameter b K=0) :
    ∃ curve : ℂ → Coupling, AnalyticAt ℂ curve 0 ∧ curve 0=K ∧
      (∀ᶠ u in 𝓝 (0:ℂ), positiveParameter b (curve u)=u) ∧
      (∀ᶠ u in 𝓝 (0:ℂ), curveB curve u=transferB K) := by
  obtain ⟨curve,hca,hc0,hq⟩ := exists_constant_anisotropy_curve hS hp
  refine ⟨curve,hca,hc0,?_,hq.mono (fun _ h => h.2)⟩
  filter_upwards [hq] with u hu
  unfold positiveParameter at he ⊢
  rw [hu.1,hu.2]
  linear_combination he

theorem exists_negative_normal_curve {K : Coupling} {b : ℝ}
    (hS : S K≠0) (hp : p K^2≠1) (he : negativeParameter b K=0) :
    ∃ curve : ℂ → Coupling, AnalyticAt ℂ curve 0 ∧ curve 0=K ∧
      (∀ᶠ u in 𝓝 (0:ℂ), negativeParameter b (curve u)=u) ∧
      (∀ᶠ u in 𝓝 (0:ℂ), negativeCurveB curve u= -transferB K) := by
  obtain ⟨curve,hca,hc0,hq⟩ := exists_constant_anisotropy_curve hS hp
  refine ⟨curve,hca,hc0,?_,hq.mono (fun _ h => congrArg Neg.neg h.2)⟩
  filter_upwards [hq] with u hu
  unfold negativeParameter at he ⊢
  rw [hu.1,hu.2]
  linear_combination he

end
end IsingBulk.Joint.Transverse
