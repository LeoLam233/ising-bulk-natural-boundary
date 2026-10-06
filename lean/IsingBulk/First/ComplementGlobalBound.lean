import IsingBulk.First.ComplementFiniteSum
import IsingBulk.First.ComplementFiniteRefinement
import IsingBulk.First.DoublePeriodicLiftIntegral

/-! The actual complementary torus integral has uniformly bounded fixed-order
s-derivatives. The finite cover, smooth partition, local estimates and seam
identities are all constructed or proved, not supplied as assumptions. -/
namespace IsingBulk.First
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff BigOperators

theorem selected_complement_global_bound {p : ℕ} {a b : ℤ}
    (hp : p.Prime) (hp11 : 11 ≤ p)
    (ha : PrimeFamily.Admissible p a) (hb : PrimeFamily.Admissible p b)
    (θ : ℝ) (hθ : 0 < Real.sin θ)
    (hS : sourceS (Complex.exp ((θ:ℂ)*Complex.I)) =
      ((2*PrimeFamily.cosineAverage p a b:ℝ):ℂ))
    (W : DoubleAngularVector (2*p) → ℝ) (hW : ContDiff ℝ ∞ W)
    (hWp : DoubleCoordinatePeriodic W)
    (hgood : ∀ u ∈ tsupport W,
      ¬ selectedBadConfiguration a b (angleTuple 1 u.1) (angleTuple 1 u.2)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
        ‖(deriv^[j] (fun s => localizedDoubleFormFactor (2*p) (sourceRadialPair θ ε).1 s W))
          (sourceRadialPair θ ε).2‖ ≤ C := by
  classical
  obtain ⟨I,w,e₀,he₀,hw,hpart,hbound⟩ :=
    selected_complement_finite_refinement hp hp11 ha hb θ hθ hS W hW hWp hgood
  obtain ⟨d,hd,_,hm⟩ := radial_disk_source_trace_margin hθ
  let ε₀ := min e₀ (d/2)
  refine ⟨ε₀,lt_min he₀ (by positivity),?_⟩
  intro j
  have hcoeff (c : I) := hbound c.1 c.2 j
  choose C hC hb using hcoeff
  refine ⟨∑ c : I, C c, Finset.sum_nonneg (fun c _ => hC c),?_⟩
  intro ε hε hεmax
  have hεe : ε ≤ e₀ := hεmax.trans (min_le_left _ _)
  have hεd : ε < d := hεmax.trans_lt ((min_le_right _ _).trans_lt (by linarith))
  have hmargin := (hm ε hε hεd (IsingBulk.Branch.radialParameter θ ε)
    (by simpa using mul_pos (show 0 < Real.sin θ/16 by positivity) hε)).2
  have hr : 0 < (sourceRadialPair θ ε).1 := Real.exp_pos _
  have hr1 : (sourceRadialPair θ ε).1 < 1 := by
    change Real.exp (-(Real.sin θ/4)*ε) < 1
    rw [Real.exp_lt_one_iff]
    exact mul_neg_of_neg_of_pos (by linarith) hε
  have hN : 0 < 2*p := Nat.mul_pos (by omega) hp.pos
  let v : I → DoubleAngularVector (2*p) → ℝ := fun c => doublePeriodicizeBump c.1.1 (w c.1)
  have hv (c : I) : Continuous (v c) :=
    (doublePeriodicizeBump_contDiff c.1.1 (w c.1) (hw c.1).1 (hw c.1).2.2).continuous
  have hsum : (fun u => ∑ c : I, v c u) = W := by
    funext u
    dsimp only [v]
    exact (Finset.sum_finset_coe
      (fun c : torusSupportBox W => doublePeriodicizeBump c.1 (w c) u) I).trans (hpart u)
  have hfun : (fun s => localizedDoubleFormFactor (2*p) (sourceRadialPair θ ε).1 s W) =
      (fun s => localizedDoubleFormFactor (2*p) (sourceRadialPair θ ε).1 s (fun u => ∑ c : I, v c u)) :=
    congrArg (fun U : DoubleAngularVector (2*p) → ℝ =>
      fun s => localizedDoubleFormFactor (2*p) (sourceRadialPair θ ε).1 s U) hsum.symm
  rw [hfun, ← iteratedDeriv_eq_iterate,
    localizedDoubleFormFactor_iteratedDeriv_sum (2*p) hN j hr hr1 (s := (sourceRadialPair θ ε).2) hmargin Finset.univ v (fun c _ => hv c)]
  calc
    ‖∑ c : I, iteratedDeriv j (fun s => localizedDoubleFormFactor (2*p)
      (sourceRadialPair θ ε).1 s (v c)) (sourceRadialPair θ ε).2‖
        ≤ ∑ c : I, ‖iteratedDeriv j (fun s => localizedDoubleFormFactor (2*p)
          (sourceRadialPair θ ε).1 s (v c)) (sourceRadialPair θ ε).2‖ := norm_sum_le _ _
    _ ≤ ∑ c : I, C c := by
      apply Finset.sum_le_sum
      intro c _
      rw [localizedDoubleFormFactor_iteratedDeriv_periodicLift (2*p) hN j hr hr1 (s := (sourceRadialPair θ ε).2) hmargin
        c.1.1 (w c.1) (hw c.1).1 (hw c.1).2.2, iteratedDeriv_eq_iterate]
      exact hb c ε hε hεe

end
end IsingBulk.First
