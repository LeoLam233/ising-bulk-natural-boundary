import IsingBulk.HT.Contour.SignedLeftDensityModel
import IsingBulk.Tail.LeftCompactSourceJets

namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail IsingBulk.Jets Set
open scoped Topology

theorem signed_left_compact_reciprocal_jet_attach (ζ : ℂ) (hζ : ‖ζ‖ = 1) {N : ℕ} (hN : 1≤N) (q : Fin N)
    (s : ℂ) (y : Fin N → ℂ) (hs : s≠0) (hy : ∀ i,y i≠0)
    (hW : ∀ i,0<(sourceW s (y i)).im) (order : ℕ) {B : ℝ} (hB : 0≤B)
    (hbound : ∀ k≤order,‖iteratedFDeriv ℂ k (fun u : ℂ × ℂ => (1-ζ*leftFrozenZ ∅ q s y u)⁻¹) 0‖≤B*(N:ℝ)^k) :
    JetBound (fun u : ℂ × ℂ => (1-ζ*leftFrozenZ ∅ q s y u)⁻¹) 0 order (B*(N:ℝ)^order) := by
  refine ⟨signed_leftFrozenZ_empty_reciprocal_analytic ζ hζ (by omega) q s y hs hy hW,by positivity,?_⟩
  intro k hk
  exact (hbound k hk).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (by exact_mod_cast hN : (1:ℝ)≤N) hk) hB)

end
end IsingBulk.HT.Contour
