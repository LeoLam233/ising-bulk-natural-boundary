import IsingBulk.HT.Tail.SignedWeightedCurrentInterval
import IsingBulk.Tail.ExactSectorNormDomination

/-! Literal signed source-sector norm sums. The original fixed partition,
named-current weights and finite multiplicities are retained. -/
namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour Set MeasureTheory
open scoped Topology BigOperators

def signedOriginalMixedSectorNorm (σ : ℂ) (N : ℕ) (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0<outer) (hi : 0< inner) (k : ℕ) (s : ℂ) : ℝ := by
  classical
  exact ∑ qa : Fin N × (Fin N → Fin 3), if ∃ j,qa.2 j=2 then
    ‖iteratedDeriv k (signedOriginalSectorIntegral σ N f r τ b outer inner ho hi (some qa)) s‖ else 0

/-- The corresponding finite current sum, with the homotopy integral
applied after the literal parameter derivative in each sector. -/
def signedIntegratedMixedSectorNorm (σ : ℂ) (N : ℕ) (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0<outer) (hi : 0< inner) (k : ℕ) (s : ℂ) (cut : ℝ) : ℝ := by
  classical
  exact ∑ q : Fin N,∑ qa : Fin N × (Fin N → Fin 3), if ∃ j,qa.2 j=2 then
    ‖∫ lam in 0..cut,iteratedDeriv k (signedCurrentSectorIntegral σ N f r τ lam q b outer inner ho hi (some qa)) s‖ else 0

theorem signedOriginalMixedSectorNorm_nonneg (σ : ℂ) (N : ℕ) (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0<outer) (hi : 0< inner) (k : ℕ) (s : ℂ) :
    0≤signedOriginalMixedSectorNorm σ N f r τ b outer inner ho hi k s := by
  classical
  unfold signedOriginalMixedSectorNorm
  exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)

theorem signedIntegratedMixedSectorNorm_nonneg (σ : ℂ) (N : ℕ) (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0<outer) (hi : 0< inner) (k : ℕ) (s : ℂ) (cut : ℝ) :
    0 ≤ signedIntegratedMixedSectorNorm σ N f r τ b outer inner ho hi k s cut := by
  classical
  unfold signedIntegratedMixedSectorNorm
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity))


def signedOriginalLeftCompactSectorNorm (σ : ℂ) (N : ℕ) (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0<outer) (hi : 0< inner) (k : ℕ) (s : ℂ) : ℝ := by
  classical
  exact ∑ qa : Fin N × (Fin N → Fin 3), if leftCompactAssignment qa.2 then
    ‖iteratedDeriv k (signedOriginalSectorIntegral σ N f r τ b outer inner ho hi (some qa)) s‖ else 0

def signedIntegratedLeftCompactSectorNorm (σ : ℂ) (N : ℕ) (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0<outer) (hi : 0< inner) (k : ℕ) (s : ℂ) (cut : ℝ) : ℝ := by
  classical
  exact ∑ q : Fin N,∑ qa : Fin N × (Fin N → Fin 3), if leftCompactAssignment qa.2 then
    ‖∫ lam in 0..cut,iteratedDeriv k (signedCurrentSectorIntegral σ N f r τ lam q b outer inner ho hi (some qa)) s‖ else 0

theorem signedOriginalLeftCompactSectorNorm_nonneg (σ : ℂ) (N : ℕ) (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0<outer) (hi : 0< inner) (k : ℕ) (s : ℂ) :
    0≤signedOriginalLeftCompactSectorNorm σ N f r τ b outer inner ho hi k s := by
  classical
  unfold signedOriginalLeftCompactSectorNorm
  exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)

theorem signedIntegratedLeftCompactSectorNorm_nonneg (σ : ℂ) (N : ℕ) (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0<outer) (hi : 0< inner) (k : ℕ) (s : ℂ) (cut : ℝ) :
    0 ≤ signedIntegratedLeftCompactSectorNorm σ N f r τ b outer inner ho hi k s cut := by
  classical
  unfold signedIntegratedLeftCompactSectorNorm
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity))


def signedOriginalRightCompactSectorNorm (σ : ℂ) (N : ℕ) (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0 < outer) (hi : 0 < inner) (k : ℕ) (s : ℂ) : ℝ := by
  classical
  exact ∑ qa : Fin N × (Fin N → Fin 3), if ∀ i, qa.2 i=1 then
    ‖iteratedDeriv k (signedOriginalSectorIntegral σ N f r τ b outer inner ho hi (some qa)) s‖ else 0

def signedIntegratedRightCompactSectorNorm (σ : ℂ) (N : ℕ) (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0 < outer) (hi : 0 < inner) (k : ℕ) (s : ℂ) (cut : ℝ) : ℝ := by
  classical
  exact ∑ q : Fin N, ∑ qa : Fin N × (Fin N → Fin 3), if ∀ i, qa.2 i=1 then
    ‖∫ lam in 0..cut, iteratedDeriv k (signedCurrentSectorIntegral σ N f r τ lam q b outer inner ho hi (some qa)) s‖ else 0

theorem signedOriginalRightCompactSectorNorm_nonneg (σ : ℂ) (N : ℕ) (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0 < outer) (hi : 0 < inner) (k : ℕ) (s : ℂ) :
    0 ≤ signedOriginalRightCompactSectorNorm σ N f r τ b outer inner ho hi k s := by
  classical
  unfold signedOriginalRightCompactSectorNorm
  exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)

theorem signedIntegratedRightCompactSectorNorm_nonneg (σ : ℂ) (N : ℕ) (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0 < outer) (hi : 0 < inner) (k : ℕ) (s : ℂ) (cut : ℝ) :
    0 ≤ signedIntegratedRightCompactSectorNorm σ N f r τ b outer inner ho hi k s cut := by
  classical
  unfold signedIntegratedRightCompactSectorNorm
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity))


def signedMixedLeftSectorNorm (σ : ℂ) (N : ℕ) (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0<outer) (hi : 0< inner) (k : ℕ) (s : ℂ) (cut : ℝ) : ℝ :=
  signedOriginalMixedSectorNorm σ N f r τ b outer inner ho hi k s+
  signedOriginalLeftCompactSectorNorm σ N f r τ b outer inner ho hi k s+
  signedIntegratedMixedSectorNorm σ N f r τ b outer inner ho hi k s cut+
  signedIntegratedLeftCompactSectorNorm σ N f r τ b outer inner ho hi k s cut


theorem signedMixedLeftSectorNorm_nonneg (σ : ℂ) (N : ℕ) (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0<outer) (hi : 0< inner) (k : ℕ) (s : ℂ) (cut : ℝ) :
    0≤signedMixedLeftSectorNorm σ N f r τ b outer inner ho hi k s cut :=
  add_nonneg (add_nonneg (add_nonneg (signedOriginalMixedSectorNorm_nonneg σ N f r τ b outer inner ho hi k s)
    (signedOriginalLeftCompactSectorNorm_nonneg σ N f r τ b outer inner ho hi k s))
    (signedIntegratedMixedSectorNorm_nonneg σ N f r τ b outer inner ho hi k s cut))
    (signedIntegratedLeftCompactSectorNorm_nonneg σ N f r τ b outer inner ho hi k s cut)


def signedRightCompactSectorNorm (σ : ℂ) (N : ℕ) (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0 < outer) (hi : 0 < inner) (J : ℕ) (s : ℂ) (cut : ℝ) : ℝ :=
  signedOriginalRightCompactSectorNorm σ N f r τ b outer inner ho hi J s+
    signedIntegratedRightCompactSectorNorm σ N f r τ b outer inner ho hi J s cut

theorem signedRightCompactSectorNorm_nonneg (σ : ℂ) (N : ℕ) (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0 < outer) (hi : 0 < inner) (J : ℕ) (s : ℂ) (cut : ℝ) :
    0 ≤ signedRightCompactSectorNorm σ N f r τ b outer inner ho hi J s cut :=
  add_nonneg (signedOriginalRightCompactSectorNorm_nonneg σ ..) (signedIntegratedRightCompactSectorNorm_nonneg σ ..)


end
end IsingBulk.HT.Tail
