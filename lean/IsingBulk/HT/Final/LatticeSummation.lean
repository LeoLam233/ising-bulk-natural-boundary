import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! Exact reflection counting for an absolutely summable full square-lattice
coefficient. These general sum identities are independent of particle parity.
They do not assume or assert that an Ising coefficient satisfies the analytic
summability hypotheses; that is a separate contour/Fourier obligation. -/
namespace IsingBulk.HT.Final
noncomputable section
open Function
open scoped BigOperators

private theorem positiveInt_injective : Injective (fun n : ℕ+ => (n:ℤ)) := by
  intro a b hab
  change ((a:ℕ):ℤ)=((b:ℕ):ℤ) at hab
  exact Subtype.ext (Int.ofNat_inj.mp hab)

/-- Integer reflection counts the origin once and each positive displacement
twice. Summability is required before any reindexing. -/
theorem tsum_int_of_reflection {f : ℤ → ℂ} (hf : Summable f)
    (heven : ∀ n : ℤ, f (-n)=f n) :
    (∑' n : ℤ, f n) = f 0+2*(∑' n : ℕ+, f (n:ℤ)) := by
  simpa only [two_nsmul, two_mul] using
    tsum_int_eq_zero_add_two_mul_tsum_pnat heven hf

/-- The full square-lattice sum has one origin, two copies of each positive
axis, and four copies of the open positive quadrant. -/
theorem full_lattice_reflection_sum {q : ℤ → ℤ → ℂ}
    (hq : Summable (Function.uncurry q))
    (hfirst : ∀ m n : ℤ, q (-m) n=q m n)
    (hsecond : ∀ m n : ℤ, q m (-n)=q m n) :
    (∑' v : ℤ × ℤ, q v.1 v.2) =
      q 0 0+
      2*(∑' m : ℕ+, q (m:ℤ) 0)+
      2*(∑' n : ℕ+, q 0 (n:ℤ))+
      4*(∑' m : ℕ+, ∑' n : ℕ+, q (m:ℤ) (n:ℤ)) := by
  have haxis : Summable (fun m : ℕ+ => q (m:ℤ) 0) := by
    change Summable (Function.uncurry q ∘ fun m : ℕ+ => ((m:ℤ),(0:ℤ)))
    apply hq.comp_injective
    intro a b hab
    exact positiveInt_injective (congrArg Prod.fst hab)
  have hquadrant : Summable (fun v : ℕ+ × ℕ+ => q (v.1:ℤ) (v.2:ℤ)) := by
    change Summable (Function.uncurry q ∘ fun v : ℕ+ × ℕ+ => ((v.1:ℤ),(v.2:ℤ)))
    apply hq.comp_injective
    intro a b hab
    apply Prod.ext
    · exact positiveInt_injective (congrArg Prod.fst hab)
    · exact positiveInt_injective (congrArg Prod.snd hab)
  have hrow (m : ℤ) : (∑' n : ℤ, q m n) =
      q m 0+2*(∑' n : ℕ+, q m (n:ℤ)) :=
    tsum_int_of_reflection (hq.prod_factor m) (hsecond m)
  have houter : (∑' m : ℤ, ∑' n : ℤ, q m n) =
      (∑' n : ℤ, q 0 n)+2*(∑' m : ℕ+, ∑' n : ℤ, q (m:ℤ) n) := by
    apply tsum_int_of_reflection hq.prod
    intro m
    exact tsum_congr (fun n => hfirst m n)
  have hpositiveRows : (∑' m : ℕ+, ∑' n : ℤ, q (m:ℤ) n) =
      (∑' m : ℕ+, q (m:ℤ) 0)+
      2*(∑' m : ℕ+, ∑' n : ℕ+, q (m:ℤ) (n:ℤ)) := by
    simp_rw [hrow]
    rw [haxis.tsum_add (hquadrant.prod.mul_left 2), tsum_mul_left]
  have hprod : (∑' v : ℤ × ℤ, q v.1 v.2) = ∑' m : ℤ, ∑' n : ℤ, q m n :=
    hq.tsum_prod
  rw [hprod, houter, hrow 0, hpositiveRows]
  ring

/-- The offsite counting convention has one copy of each positive axis and
two copies of the open positive quadrant, exactly as the contour kernel. -/
def positiveOffsiteMass (q : ℤ → ℤ → ℂ) : ℂ :=
  (∑' m : ℕ+, q (m:ℤ) 0)+
  (∑' n : ℕ+, q 0 (n:ℤ))+
  2*(∑' m : ℕ+, ∑' n : ℕ+, q (m:ℤ) (n:ℤ))

/-- Algebraic full-site identity after the genuine full lattice sum has
been shown summable. No diagonal restriction or particle truncation occurs. -/
theorem full_lattice_eq_onsite_add_two_offsite {q : ℤ → ℤ → ℂ}
    (hq : Summable (Function.uncurry q))
    (hfirst : ∀ m n : ℤ, q (-m) n=q m n)
    (hsecond : ∀ m n : ℤ, q m (-n)=q m n) :
    (∑' v : ℤ × ℤ, q v.1 v.2) = q 0 0+2*positiveOffsiteMass q := by
  rw [full_lattice_reflection_sum hq hfirst hsecond]
  unfold positiveOffsiteMass
  ring

end
end IsingBulk.HT.Final
