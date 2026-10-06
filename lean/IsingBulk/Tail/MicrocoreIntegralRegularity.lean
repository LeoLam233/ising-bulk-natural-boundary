import IsingBulk.Tail.CompactSupportLie
import IsingBulk.Analysis.LieLocal

/-! Support and regularity bridges for actual microcore integral stages.
No quantitative jet bound or sector estimate is a premise. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Lie Set Function
open scoped ContDiff Topology

theorem iterate_lieStep_zero {n : ℕ}
    (V : ℂ → AngularSpace n → Fin (n+1) → ℂ) (j : ℕ) :
    (lieStep V)^[j] (fun _ _ => (0:ℂ)) = (fun _ _ => 0) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply',ih]
    funext s x
    simp [IsingBulk.Lie.lieStep,IsingBulk.Lie.divergence]

theorem iterate_lieStep_support_subset {n : ℕ}
    (V : ℂ → AngularSpace n → Fin (n+1) → ℂ) (A : ℂ → AngularSpace n → ℂ)
    {U : Set ℂ} (hU : IsOpen U) {K : Set (AngularSpace n)} (hK : IsClosed K)
    (hsupp : ∀ s ∈ U, support (A s) ⊆ K) (j : ℕ) :
    ∀ s ∈ U, tsupport (((lieStep V)^[j] A) s) ⊆ K := by
  have he : ∀ s ∈ U, EqOn (A s) (fun _ => (0:ℂ)) Kᶜ := by
    intro s hs x hx
    exact notMem_support.mp (fun hn => hx (hsupp s hs hn))
  have hj := iterate_lieStep_congr_on V hU hK.isOpen_compl he j
  rw [iterate_lieStep_zero] at hj
  intro s hs
  apply closure_minimal _ hK
  intro x hx
  by_contra hxK
  exact hx (hj s hs hxK)

theorem weighted_contDiff_on_fixed_support {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {K : Set E} (w : E → ℝ) (F : E → ℂ)
    (hw : ContDiff ℝ ∞ w) (hsupp : tsupport w ⊆ K)
    (hF : ∀ x ∈ K, ContDiffAt ℝ ∞ F x) :
    ContDiff ℝ ∞ (fun x => (w x:ℂ)*F x) :=
  weighted_contDiff_of_tsupport w F hw (fun x hx => hF x (hsupp hx))

end
end IsingBulk.Tail
