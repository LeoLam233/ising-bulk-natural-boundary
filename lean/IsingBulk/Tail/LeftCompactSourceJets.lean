import IsingBulk.Tail.LeftCompactDensityModel
import IsingBulk.Tail.RadialSourceDomain

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets Set
open scoped Topology

theorem mixedBranchIndexSet_empty {N : ℕ} (sigma : Fin N → Fin 3) (h : ∀ i,sigma i≠2) :
    mixedBranchIndexSet sigma=∅ := by
  ext i
  simp [mixedBranchIndexSet,h i]

theorem deformed_sourceW_upper_on_damping {N : ℕ} (hN : 0<N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ lam : ℝ}
    (hr : 0<r) (hr1 : r<1) (hτ : 0≤τ) (hl : 0≤lam)
    {s : ℂ} (hs : s∈dampingDomain r) (θ : Fin N → ℝ) (i : Fin N) :
    0<(sourceW s (deformedPoint f r τ lam θ i)).im := by
  have hh := sourceW_upper_of_margin hr hr1 hs.2 (deformedPoint_zero_norm f hr.le τ θ i)
  exact hh.trans_le (deformed_sourceW_im_ge hN f hr hτ hl θ s
    hf.p_nonneg hf.m_nonneg hf.p_zero hf.m_zero i)

theorem left_compact_reciprocal_jet_attach {N : ℕ} (hN : 1≤N) (q : Fin N)
    (s : ℂ) (y : Fin N → ℂ) (hs : s≠0) (hy : ∀ i,y i≠0)
    (hW : ∀ i,0<(sourceW s (y i)).im) (order : ℕ) {B : ℝ} (hB : 0≤B)
    (hbound : ∀ k≤order,‖iteratedFDeriv ℂ k (fun u : ℂ × ℂ => (1-leftFrozenZ ∅ q s y u)⁻¹) 0‖≤B*(N:ℝ)^k) :
    JetBound (fun u : ℂ × ℂ => (1-leftFrozenZ ∅ q s y u)⁻¹) 0 order (B*(N:ℝ)^order) := by
  refine ⟨leftFrozenZ_empty_reciprocal_analytic (by omega) q s y hs hy hW,by positivity,?_⟩
  intro k hk
  exact (hbound k hk).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (by exact_mod_cast hN : (1:ℝ)≤N) hk) hB)

end
end IsingBulk.Tail
