import IsingBulk.AnisoF002.C03.IsotropicProtectedSecants

/-!
# Joint analyticity of the actual covariance transport field

The field is the existing `rightCovarianceField`, with actual parameter
derivatives, actual filled secants, and complete population variance.
At every nonconstant real right tuple it is jointly analytic, with no
exclusion of partial diagonals, and has both exact transport identities.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Filter Set Metric

def jointParameterDerivative (U : ℂ × ℂ → ℂ) (q : ℂ × ℂ) : ℂ :=
  deriv (fun S => U (S, q.2)) q.1

theorem jointParameterDerivative_analyticAt (U : ℂ × ℂ → ℂ) (q : ℂ × ℂ)
    (hU : AnalyticAt ℂ U q) : AnalyticAt ℂ (jointParameterDerivative U) q := by
  have hL : AnalyticAt ℂ (fun p => fderiv ℂ U p ((1, 0) : ℂ × ℂ)) q :=
    ((ContinuousLinearMap.apply ℂ ℂ ((1, 0) : ℂ × ℂ)).analyticAt _).comp hU.fderiv
  apply hL.congr
  filter_upwards [hU.eventually_analyticAt] with p hp
  exact (hp.differentiableAt.hasFDerivAt.comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))).deriv.symm

variable {ι : Type*} [Fintype ι]

theorem coordinate_analyticAt (q : ℂ × (ι → ℂ)) (i : ι) :
    AnalyticAt ℂ (fun p : ℂ × (ι → ℂ) => p.2 i) q :=
  ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt q.2).comp analyticAt_snd

theorem rightCovarianceAmplitude_analyticAt (q : ℂ × (ι → ℂ))
    (hU : ∀ i, AnalyticAt ℂ explicitRightInverse (q.1, q.2 i)) :
    AnalyticAt ℂ (fun p : ℂ × (ι → ℂ) => rightCovarianceAmplitude p.1 p.2) q := by
  apply AnalyticAt.neg
  apply Finset.analyticAt_fun_sum
  intro i _
  exact (jointParameterDerivative_analyticAt explicitRightInverse (q.1, q.2 i) (hU i)).comp
    (f := fun p : ℂ × (ι → ℂ) => (p.1, p.2 i))
    (analyticAt_fst.prod (coordinate_analyticAt q i))

theorem actual_pairVariance_analyticAt (q : ℂ × (ι → ℂ))
    (hU : ∀ i, AnalyticAt ℂ explicitRightInverse (q.1, q.2 i)) :
    AnalyticAt ℂ (fun p : ℂ × (ι → ℂ) =>
      pairVariance (fun i => explicitRightInverse (p.1, p.2 i))) q := by
  apply AnalyticAt.mul analyticAt_const
  apply Finset.analyticAt_fun_sum
  intro i _
  apply Finset.analyticAt_fun_sum
  intro j _
  exact (((hU i).comp (f := fun p : ℂ × (ι → ℂ) => (p.1, p.2 i))
    (analyticAt_fst.prod (coordinate_analyticAt q i))).sub
    ((hU j).comp (f := fun p : ℂ × (ι → ℂ) => (p.1, p.2 j))
      (analyticAt_fst.prod (coordinate_analyticAt q j)))).pow 2

/-- Analyticity of the existing field follows from its actual filled
secants and actual nonzero complete variance. -/
theorem rightCovarianceField_analyticAt (q : ℂ × (ι → ℂ))
    (hU : ∀ i, AnalyticAt ℂ explicitRightInverse (q.1, q.2 i))
    (hfirst : ∀ i j, AnalyticAt ℂ (jointFirstSecant explicitRightInverse)
      (q.1, q.2 i, q.2 j))
    (hsecond : ∀ i j, AnalyticAt ℂ (jointSecondSecant explicitRightInverse)
      (q.1, q.2 i, q.2 j))
    (hsecond_ne : ∀ i j, jointSecondSecant explicitRightInverse (q.1, q.2 i, q.2 j) ≠ 0)
    (hvar : pairVariance (fun i => explicitRightInverse (q.1, q.2 i)) ≠ 0) :
    AnalyticAt ℂ (fun p : ℂ × (ι → ℂ) => rightCovarianceField p.1 p.2) q := by
  apply AnalyticAt.pi
  intro i
  have hpair : ∀ j, AnalyticAt ℂ (fun p : ℂ × (ι → ℂ) =>
      analyticSecantPair (fun z => explicitRightInverse (p.1, z)) p.2 i j) q := by
    intro j
    have hmap : AnalyticAt ℂ (fun p : ℂ × (ι → ℂ) => (p.1, p.2 i, p.2 j)) q :=
      analyticAt_fst.prod ((coordinate_analyticAt q i).prod (coordinate_analyticAt q j))
    have hf := (hfirst i j).comp
      (f := fun p : ℂ × (ι → ℂ) => (p.1, p.2 i, p.2 j)) hmap
    have hs := (hsecond i j).comp
      (f := fun p : ℂ × (ι → ℂ) => (p.1, p.2 i, p.2 j)) hmap
    exact (((coordinate_analyticAt q i).sub (coordinate_analyticAt q j)).mul
      (hf.pow 2)).div hs (hsecond_ne i j)
  have hsum := Finset.analyticAt_fun_sum Finset.univ (fun j _ => hpair j)
  exact ((rightCovarianceAmplitude_analyticAt q hU).mul hsum).div
    (actual_pairVariance_analyticAt q hU) hvar

/-- The actual field is regular at every partial diagonal on the real
right arc. Only total equality is excluded; its variance would be zero.
The local joint analytic statement is integrated with the exact phase
and angular-sum transport identities of the same field. -/
theorem rightCovarianceField_real_right_analytic_transport
    (S : ℝ) (hS : 0 < S ∧ S < 2) (N : ℕ) (w : Fin N → ℝ)
    (hw : ∀ i, w i ∈ Icc (-rightBranchEndpoint S) 0)
    (i j : Fin N) (hij : w i ≠ w j) :
    let v : Fin N → ℂ := fun k => (rightArcCoordinate S (w k) : ℂ)
    AnalyticAt ℂ (fun p : ℂ × (Fin N → ℂ) => rightCovarianceField p.1 p.2) ((S : ℂ), v) ∧
      (∑ k, rightCovarianceField (S : ℂ) v k) = 0 ∧
      (∑ k, deriv (fun z => explicitRightInverse ((S : ℂ), z)) (v k) *
        rightCovarianceField (S : ℂ) v k) = rightCovarianceAmplitude (S : ℂ) v ∧
      HasDerivAt (fun t : ℂ => ∑ k,
        ((v k + t * rightCovarianceField (S : ℂ) v k) -
          explicitRightInverse ((S : ℂ) + t,
            v k + t * rightCovarianceField (S : ℂ) v k))) 0 0 := by
  dsimp only
  let v : Fin N → ℂ := fun k => (rightArcCoordinate S (w k) : ℂ)
  have hv : ∀ k, v k ∈ Complex.ofReal '' Icc (-rightBranchEndpoint S) (rightBranchEndpoint S) := by
    intro k
    refine ⟨rightArcCoordinate S (w k), ?_, rfl⟩
    rw [← rightArcCoordinate_image S hS]
    exact ⟨w k, hw k, rfl⟩
  have hp : ∀ k l, ((S : ℂ), v k, v l) ∈ rightPairParameterSegment S :=
    fun k l => ⟨rfl, hv k, hv l⟩
  obtain ⟨r, c, _, hc, _, hfirst, hsecond, _, hlower, _⟩ :=
    exists_right_secants_protected_neighborhood S hS
  have hpa : AnalyticAt ℂ (fun p : ℂ × (Fin N → ℂ) => rightCovarianceField p.1 p.2)
      ((S : ℂ), v) := by
    apply rightCovarianceField_analyticAt
    · intro k
      exact (explicitRightInverse_data_on_arc S (w k) hS (hw k)).1
    · intro k l
      exact hfirst _ (self_subset_cthickening _ (hp k l))
    · intro k l
      exact hsecond _ (self_subset_cthickening _ (hp k l))
    · intro k l hz
      have h := hlower _ (self_subset_cthickening _ (hp k l))
      rw [hz, Complex.zero_re] at h
      linarith
    · exact rightArc_pairVariance_ne_zero S hS w hw i j hij
  exact ⟨hpa, rightCovarianceField_on_real_right_arc S hS N w hw i j hij⟩

end IsingBulk.AnisoF002.Isotropic
