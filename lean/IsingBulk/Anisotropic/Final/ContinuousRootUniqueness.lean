import IsingBulk.Anisotropic.Final.NormalizedRoot
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Connected.TotallyDisconnected

namespace IsingBulk.Anisotropic
noncomputable section
open Set

theorem fourthRootsOfOne_finite : Set.Finite {z : ℂ | z^4=1} := by
  have hp : (Polynomial.X^4 - 1 : Polynomial ℂ) ≠ 0 := by
    intro he
    have hh := congrArg (Polynomial.eval (0:ℂ)) he
    norm_num at hh
  simpa [Polynomial.IsRoot,sub_eq_zero] using Polynomial.finite_setOfPred_isRoot hp

theorem continuous_fourth_roots_eqOn {X : Type*} [TopologicalSpace X] {U : Set X}
    (hU : IsPreconnected U) {f g : X → ℂ} (hf : ContinuousOn f U)
    (hg : ContinuousOn g U) (hn : ∀ x∈U, g x≠0)
    (hp : ∀ x∈U, f x^4=g x^4) {x₀ : X} (hx₀ : x₀∈U)
    (hb : f x₀=g x₀) : EqOn f g U := by
  have hc : ContinuousOn (fun x => f x/g x) U := hf.div hg hn
  have hm : MapsTo (fun x => f x/g x) U {z : ℂ | z^4=1} := by
    intro x hx
    change (f x/g x)^4=1
    rw [div_pow,hp x hx,div_self (pow_ne_zero _ (hn x hx))]
  intro x hx
  have hh := hU.constant_of_mapsTo fourthRootsOfOne_finite.isDiscrete hc hm hx hx₀
  rw [hb,div_self (hn x₀ hx₀)] at hh
  exact (div_eq_one_iff_eq (hn x hx)).mp hh

end
end IsingBulk.Anisotropic
