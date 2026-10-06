import IsingBulk.Tail.HighKSBound
import IsingBulk.Tail.GlobalAnalytic

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch

/-- Summability of the actual K plus small-current norm sequence, with one
geometric epsilon neighborhood before all derivative orders and split points. -/
theorem actual_originalKS_summable (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ eta0 : ℝ, 0<eta0 ∧ ∀ eta : ℝ, 0<eta → eta<eta0 →
      ∃ alpha0 tau0 : ℝ, 0<alpha0 ∧ 0<tau0 ∧ ∀ alpha tau : ℝ,
        0<alpha → alpha<alpha0 → 0<tau → tau<tau0 →
        ∃ epsilon0 : ℝ, 0<epsilon0 ∧ ∀ (j : ℕ) (eps cut : ℝ),
          0<eps → eps<epsilon0 → 0≤cut → cut≤1 →
          Summable (fun N : ℕ => if 2≤N then
            originalKSNorm N (constructedSelector d.thetaB eta alpha) (Real.exp (-d.c₀*eps)) tau j
              (radialParameter d.theta eps) cut else 0) := by
  obtain ⟨eta0,he0,hmain⟩ := actual_highKS_gaussian_bound d hcsmall
  refine ⟨eta0,he0,?_⟩
  intro eta he heL
  obtain ⟨alpha0,tau0,ha0,ht0,hsetup⟩ := hmain eta he heL
  refine ⟨alpha0,tau0,ha0,ht0,?_⟩
  intro alpha tau ha haL ht htL
  obtain ⟨c,e,K,C,kappa,hc,heps,hK,hC,hk,hbound⟩ := hsetup alpha tau ha haL ht htL
  refine ⟨e,heps,?_⟩
  intro j eps cut he heL hcut hcut1
  have hs := (summable_source_gaussian hC.le hk 0).mul_left
    (((j.factorial:ℝ)*c⁻¹^j*K)*eps⁻¹^(j+2))
  simp only [pow_zero,mul_one] at hs
  apply hs.of_nonneg_of_le
  · intro N
    split_ifs
    · exact originalKSNorm_nonneg _ _ _ _ _ _ _
    · exact le_refl 0
  · intro N
    split_ifs with hN
    · have hb := hbound j N eps cut hN he heL hcut hcut1
      convert hb using 1
      ring
    · positivity

end
end IsingBulk.Tail
