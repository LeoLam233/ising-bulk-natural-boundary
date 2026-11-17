import IsingBulk.AnisoF002.C03.IsotropicTransportWords
import IsingBulk.AnisoF002.C03.IsotropicAnalyticDescendantPullback

/-!
# The complete actual transport recurrence is the finite word sum

The induction is an equality of germs before each subsequent derivative.
Every covariance derivative, parameter-dependent coefficient, and smooth
cutoff derivative is retained. No pointwise identity is differentiated
without its neighborhood equality.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators ContDiff
open Filter

def actualSeparatedWordSum {N : ℕ} (η τ ξ : ℝ) (F : RegularJointSpace N → ℂ)
    (g : (Fin N → ℝ) → ℂ) (n : ℕ) (x : ℂ × (Fin N → ℝ)) : ℂ :=
  ∑ w : TransportWord N n,
    transportAnalyticWord (fun p : RegularJointSpace N => rightCovarianceField p.1 p.2)
      rightCutoffTransportCoefficient F n w (regularJointMap (actualPhysicalCoordinate η τ ξ) x) *
    transportAngularWord (actualBalancedInverseEntry η τ ξ) g n w x.2

theorem actualSeparatedWordSum_zero {N : ℕ} (η τ ξ : ℝ) (F : RegularJointSpace N → ℂ)
    (g : (Fin N → ℝ) → ℂ) (x : ℂ × (Fin N → ℝ)) :
    actualSeparatedWordSum η τ ξ F g 0 x = F (regularJointMap (actualPhysicalCoordinate η τ ξ) x) * g x.2 := by
  simp only [actualSeparatedWordSum, transportAnalyticWord, transportAngularWord,
    Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, pow_zero, one_nsmul]

theorem actualSeparatedWordSum_step {N : ℕ} (η τ ξ : ℝ)
    (F : RegularJointSpace N → ℂ) (g : (Fin N → ℝ) → ℂ)
    (x : ℂ × (Fin N → ℝ))
    (hχ : ∀ i, DifferentiableAt ℝ (actualPhysicalCoordinate η τ ξ i) x)
    (hB : AnalyticAt ℂ (fun p : RegularJointSpace N => rightCovarianceField p.1 p.2)
      (regularJointMap (actualPhysicalCoordinate η τ ξ) x))
    (hK : ∀ j, AnalyticAt ℂ (fun p : RegularJointSpace N => rightCutoffTransportCoefficient p j)
      (regularJointMap (actualPhysicalCoordinate η τ ξ) x))
    (hF : AnalyticAt ℂ F (regularJointMap (actualPhysicalCoordinate η τ ξ) x))
    (hA : ∀ i j, ContDiffAt ℝ ∞ (actualBalancedInverseEntry η τ ξ i j) x.2)
    (hg : ContDiffAt ℝ ∞ g x.2)
    (hdet : actualCoordinateDeterminant η τ ξ x ≠ 0)
    (hV : ∀ i, actualCovarianceAngularVelocity η τ ξ i x =
      -∑ j, actualBalancedInverseEntry η τ ξ i j x.2 *
        rightCutoffTransportCoefficient (regularJointMap (actualPhysicalCoordinate η τ ξ) x) j)
    (n : ℕ) :
    actualTransportAmplitude η τ ξ (actualSeparatedWordSum η τ ξ F g n) x =
      actualSeparatedWordSum η τ ξ F g (n + 1) x := by
  let B : RegularJointSpace N → Fin N → ℂ := fun p => rightCovarianceField p.1 p.2
  let K : RegularJointSpace N → Fin N → ℂ := rightCutoffTransportCoefficient
  let A := actualBalancedInverseEntry (N := N) η τ ξ
  let q := regularJointMap (actualPhysicalCoordinate η τ ξ) x
  have hm : DifferentiableAt ℝ (regularJointMap (actualPhysicalCoordinate η τ ξ)) x :=
    differentiableAt_fst.prodMk (differentiableAt_pi.mpr hχ)
  have hFw (w : TransportWord N n) : AnalyticAt ℂ (transportAnalyticWord B K F n w) q :=
    transportAnalyticWord_analyticAt B K F q hB hK hF n w
  have hgw (w : TransportWord N n) :
      ContDiffAt ℝ ∞ (transportAngularWord A g n w) x.2 :=
    transportAngularWord_contDiffAt A g x.2 hA hg n w
  have hdiff (w : TransportWord N n) : DifferentiableAt ℝ
      (fun y => transportAnalyticWord B K F n w
        (regularJointMap (actualPhysicalCoordinate η τ ξ) y) * transportAngularWord A g n w y.2) x :=
    (((hFw w).restrictScalars.differentiableAt).comp x hm).mul
      (((hgw w).differentiableAt (by simp)).comp x differentiableAt_snd)
  change regularTransportAmplitude (actualPhysicalCoordinate η τ ξ) actualAngularDirection
    actualTimeDirection (actualCovarianceRegularField η τ ξ)
    (fun y => ∑ w : TransportWord N n, transportAnalyticWord B K F n w
      (regularJointMap (actualPhysicalCoordinate η τ ξ) y) * transportAngularWord A g n w y.2) x = _
  rw [regularTransportAmplitude_sum _ _ _ _ _ _ hdiff hdet]
  have hs (w : TransportWord N n) := actualTransport_separated_product η τ ξ
    (transportAnalyticWord B K F n w) (transportAngularWord A g n w) x hχ hB.differentiableAt
    (hFw w).differentiableAt ((hgw w).differentiableAt (by simp)) hdet hV
  change (∑ w : TransportWord N n, actualTransportAmplitude η τ ξ
    (fun y => transportAnalyticWord B K F n w
      (regularJointMap (actualPhysicalCoordinate η τ ξ) y) * transportAngularWord A g n w y.2) x) = _
  simp_rw [hs]
  rw [actualSeparatedWordSum, transportWord_sum_succ]
  simp only [Fintype.sum_option, Fintype.sum_prod_type, transportAnalyticWord,
    transportAngularWord, Fin.cons_zero, Fin.cons_succ, Finset.sum_add_distrib]
  change (∑ w : TransportWord N n, analyticTransportAmplitude B (transportAnalyticWord B K F n w) q *
      transportAngularWord A g n w x.2) +
    (∑ w : TransportWord N n, ∑ i, ∑ j,
      (transportAnalyticWord B K F n w q * K q j) *
        (A i j x.2 * realAngularPartial (transportAngularWord A g n w) i x.2)) = _
  have hswap : (∑ w : TransportWord N n, ∑ i, ∑ j,
      (transportAnalyticWord B K F n w q * K q j) *
        (A i j x.2 * realAngularPartial (transportAngularWord A g n w) i x.2)) =
    (∑ i, ∑ j, ∑ w : TransportWord N n,
      (transportAnalyticWord B K F n w q * K q j) *
        (A i j x.2 * realAngularPartial (transportAngularWord A g n w) i x.2)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
  rw [hswap]

theorem actualTransportDescendant_eq_separated_words {N : ℕ} (η τ ξ : ℝ)
    (F : RegularJointSpace N → ℂ) (g : (Fin N → ℝ) → ℂ)
    (hA : ∀ i j : Fin N, ContDiff ℝ ∞ (actualBalancedInverseEntry η τ ξ i j))
    (hg : ContDiff ℝ ∞ g)
    (x : ℂ × (Fin N → ℝ))
    (hχ : ∀ i, ContDiffAt ℝ 2 (actualPhysicalCoordinate η τ ξ i) x)
    (hB : AnalyticAt ℂ (fun p : RegularJointSpace N => rightCovarianceField p.1 p.2)
      (regularJointMap (actualPhysicalCoordinate η τ ξ) x))
    (hK : ∀ j, AnalyticAt ℂ (fun p : RegularJointSpace N => rightCutoffTransportCoefficient p j)
      (regularJointMap (actualPhysicalCoordinate η τ ξ) x))
    (hF : AnalyticAt ℂ F (regularJointMap (actualPhysicalCoordinate η τ ξ) x))
    (hdet : actualCoordinateDeterminant η τ ξ x ≠ 0)
    (hV : ∀ᶠ y in 𝓝 x, ∀ i, actualCovarianceAngularVelocity η τ ξ i y =
      -∑ j, actualBalancedInverseEntry η τ ξ i j y.2 *
        rightCutoffTransportCoefficient (regularJointMap (actualPhysicalCoordinate η τ ξ) y) j)
    (n : ℕ) :
    actualTransportDescendant η τ ξ
      (fun y => F (regularJointMap (actualPhysicalCoordinate η τ ξ) y) * g y.2) n x =
      actualSeparatedWordSum η τ ξ F g n x := by
  induction n generalizing x with
  | zero => exact (actualSeparatedWordSum_zero η τ ξ F g x).symm
  | succ n ih =>
    have hχd (i : Fin N) : DifferentiableAt ℝ (actualPhysicalCoordinate η τ ξ i) x :=
      (hχ i).differentiableAt (by norm_num)
    have hm : ContinuousAt (regularJointMap (actualPhysicalCoordinate η τ ξ)) x :=
      continuousAt_fst.prodMk (continuousAt_pi.mpr (fun i => (hχd i).continuousAt))
    have hχnear : ∀ᶠ y in 𝓝 x, ∀ i, ContDiffAt ℝ 2 (actualPhysicalCoordinate η τ ξ i) y :=
      Filter.eventually_all.mpr (fun i => (hχ i).eventually (by norm_num))
    have hdnear : ∀ᶠ y in 𝓝 x, actualCoordinateDeterminant η τ ξ y ≠ 0 :=
      (scalarCoordinateDet_differentiableAt (actualPhysicalCoordinate η τ ξ)
        actualAngularDirection x hχ).continuousAt.eventually_ne hdet
    have hBnear := hm.eventually hB.eventually_analyticAt
    have hKnear : ∀ᶠ y in 𝓝 x, ∀ j, AnalyticAt ℂ
        (fun p : RegularJointSpace N => rightCutoffTransportCoefficient p j)
        (regularJointMap (actualPhysicalCoordinate η τ ξ) y) :=
      Filter.eventually_all.mpr (fun j => hm.eventually (hK j).eventually_analyticAt)
    have hFnear := hm.eventually hF.eventually_analyticAt
    have hVnear := eventually_eventually_nhds.mpr hV
    have heq : actualTransportDescendant η τ ξ
        (fun y => F (regularJointMap (actualPhysicalCoordinate η τ ξ) y) * g y.2) n =ᶠ[𝓝 x]
        actualSeparatedWordSum η τ ξ F g n := by
      filter_upwards [hχnear, hdnear, hBnear, hKnear, hFnear, hVnear] with y hχy hdy hBy hKy hFy hVy
      exact ih y hχy hBy hKy hFy hdy hVy
    rw [actualTransportDescendant_succ]
    change regularTransportAmplitude (actualPhysicalCoordinate η τ ξ) actualAngularDirection
      actualTimeDirection (actualCovarianceRegularField η τ ξ) _ x = _
    rw [regularTransportAmplitude_congr_germ _ _ _ _ _ _ _ heq]
    exact actualSeparatedWordSum_step η τ ξ F g x hχd hB hK hF
      (fun i j => (hA i j).contDiffAt) hg.contDiffAt hdet hV.self_of_nhds n

end IsingBulk.AnisoF002.Isotropic
