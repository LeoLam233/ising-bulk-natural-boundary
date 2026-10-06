import IsingBulk.Tail.RealReciprocalJets
import IsingBulk.Tail.CompactSelectedField

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First Set Filter
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
set_option maxHeartbeats 1500000

def selectedPairJetConstant (J : ℕ) (B c : ℝ) : ℝ :=
  2*(2^J*(2^J*B*B)*((J.factorial:ℝ)^2*(max 1 c⁻¹)^(J+1)*(max 1 B)^J))

theorem selected_pair_scaled_jets {N : ℕ}
    (A : Fin N → E → ℂ) (Q D : E → ℂ) (x : E) (i j l : Fin N)
    (J : ℕ) (ρ c B : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hc : 0 < c)
    (hA : ∀ k, RealScaledJetBound (A k) x J 1 B 0)
    (hQ : RealScaledJetBound Q x J 1 B 0)
    (hD : RealScaledJetBound D x J 1 B 0) (hgap : c*ρ ≤ ‖D x‖) :
    RealScaledJetBound (fun y => cancelledAngularPair (fun k => A k y) (Q y) (D y) i j l)
      x J ρ (selectedPairJetConstant J B c) (-1) := by
  have hr := real_reciprocal_scaled_jets D x J ρ c B hD.smooth hρ hρ1 hc hgap
    (fun k _ hk => by simpa using hD.bound k hk)
  have hq := hQ.rescale_zero hρ hρ1
  have ha (k : Fin N) := (hA k).rescale_zero hρ hρ1
  have hp (k : Fin N) := (hq.mul (ha k) hρ).mul hr hρ
  have hconst : 0 ≤ 2^J*(2^J*B*B)*
      ((J.factorial:ℝ)^2*(max 1 c⁻¹)^(J+1)*(max 1 B)^J) := by
    have := hQ.nonneg
    positivity
  have hleft : RealScaledJetBound (fun y => if l=i then -(Q y*A j y*(D y)⁻¹) else 0)
      x J ρ (2^J*(2^J*B*B)*((J.factorial:ℝ)^2*(max 1 c⁻¹)^(J+1)*(max 1 B)^J)) (-1) := by
    by_cases hli : l=i
    · simpa only [hli,ite_true,zero_add] using (hp j).neg
    · simpa only [hli,ite_false] using RealScaledJetBound.zero x J ρ _ (-1) hρ.le hconst
  have hright : RealScaledJetBound (fun y => if l=j then Q y*A i y*(D y)⁻¹ else 0)
      x J ρ (2^J*(2^J*B*B)*((J.factorial:ℝ)^2*(max 1 c⁻¹)^(J+1)*(max 1 B)^J)) (-1) := by
    by_cases hlj : l=j
    · simpa only [hlj,ite_true,zero_add] using hp i
    · simpa only [hlj,ite_false] using RealScaledJetBound.zero x J ρ _ (-1) hρ.le hconst
  have hh := hleft.add hright
  simpa only [selectedPairJetConstant,two_mul,cancelledAngularPair,Pi.add_apply,
    Pi.single_apply,div_eq_mul_inv,neg_mul] using hh

end
end IsingBulk.Tail
