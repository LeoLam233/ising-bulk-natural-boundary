import IsingBulk.AnisoF002.C03.IsotropicTransportWords
import IsingBulk.AnisoF002.C03.IsotropicAnalyticDescendantPullback

/-!
# Exact separated transport for any genuine regular field

This additive generalization retains the full real cutoff and inverse
balanced Jacobian. It will be specialized to the named-anchor field;
its complete physical kernel is part of the analytic amplitude.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators ContDiff
open Filter

def coordinateRegularField {N : ℕ} (B : RegularJointSpace N → Fin N → ℂ) (η τ ξ : ℝ)
    (i : Fin N) (q : ℂ × (Fin N → ℝ)) : ℂ :=
  B (regularJointMap (actualPhysicalCoordinate η τ ξ) q) i

def coordinateAngularVelocity {N : ℕ} (B : RegularJointSpace N → Fin N → ℂ) (η τ ξ : ℝ)
    (i : Fin N) (q : ℂ × (Fin N → ℝ)) : ℂ :=
  constructedAngularVelocity (actualPhysicalCoordinate η τ ξ) actualAngularDirection
    actualTimeDirection (coordinateRegularField B η τ ξ) i q

def coordinateTransportAmplitude {N : ℕ} (B : RegularJointSpace N → Fin N → ℂ) (η τ ξ : ℝ)
    (b : (ℂ × (Fin N → ℝ)) → ℂ) : (ℂ × (Fin N → ℝ)) → ℂ :=
  regularTransportAmplitude (actualPhysicalCoordinate η τ ξ) actualAngularDirection
    actualTimeDirection (coordinateRegularField B η τ ξ) b

def coordinateTransportDescendant {N : ℕ} (B : RegularJointSpace N → Fin N → ℂ) (η τ ξ : ℝ)
    (b : (ℂ × (Fin N → ℝ)) → ℂ) : ℕ → (ℂ × (Fin N → ℝ)) → ℂ :=
  regularTransportDescendant (actualPhysicalCoordinate η τ ξ) actualAngularDirection
    actualTimeDirection (coordinateRegularField B η τ ξ) b

theorem coordinateTransport_separated_product {N : ℕ} (B K : RegularJointSpace N → Fin N → ℂ) (η τ ξ : ℝ)
    (F : RegularJointSpace N → ℂ) (g : (Fin N → ℝ) → ℂ)
    (x : ℂ × (Fin N → ℝ))
    (hχ : ∀ i, DifferentiableAt ℝ (actualPhysicalCoordinate η τ ξ i) x)
    (hB : DifferentiableAt ℂ B
      (regularJointMap (actualPhysicalCoordinate η τ ξ) x))
    (hF : DifferentiableAt ℂ F (regularJointMap (actualPhysicalCoordinate η τ ξ) x))
    (hg : DifferentiableAt ℝ g x.2)
    (hdet : actualCoordinateDeterminant η τ ξ x ≠ 0)
    (hV : ∀ i, coordinateAngularVelocity B η τ ξ i x =
      -∑ j, actualBalancedInverseEntry η τ ξ i j x.2 *
        K (regularJointMap (actualPhysicalCoordinate η τ ξ) x) j) :
    coordinateTransportAmplitude B η τ ξ
      (fun y => F (regularJointMap (actualPhysicalCoordinate η τ ξ) y) * g y.2) x =
      analyticTransportAmplitude B F
        (regularJointMap (actualPhysicalCoordinate η τ ξ) x) * g x.2 +
      ∑ i, ∑ j,
        (F (regularJointMap (actualPhysicalCoordinate η τ ξ) x) *
          K (regularJointMap (actualPhysicalCoordinate η τ ξ) x) j) *
          (actualBalancedInverseEntry η τ ξ i j x.2 * realAngularPartial g i x.2) := by
  have hm : DifferentiableAt ℝ (regularJointMap (actualPhysicalCoordinate η τ ξ)) x :=
    differentiableAt_fst.prodMk (differentiableAt_pi.mpr hχ)
  have hFp : DifferentiableAt ℝ
      (fun y => F (regularJointMap (actualPhysicalCoordinate η τ ξ) y)) x :=
    (hF.restrictScalars (𝕜 := ℝ)).comp x hm
  have hgp : DifferentiableAt ℝ (fun y : ℂ × (Fin N → ℝ) => g y.2) x :=
    hg.comp x differentiableAt_snd
  rw [coordinateTransportAmplitude, regularTransportAmplitude_mul _ _ _ _ _ _ _ hFp hgp hdet]
  have ht := regularTransportAmplitude_joint_pullback (actualPhysicalCoordinate η τ ξ)
    B F x hχ hB hF hdet
  change regularTransportAmplitude (actualPhysicalCoordinate η τ ξ) actualAngularDirection
    actualTimeDirection (coordinateRegularField B η τ ξ)
    (fun y => F (regularJointMap (actualPhysicalCoordinate η τ ξ) y)) x = _ at ht
  rw [ht, scalarTransportDerivative_angular_lift _ g x hg]
  change _ + _ * (-∑ i, coordinateAngularVelocity B η τ ξ i x * _) = _
  simp_rw [hV]
  simp only [neg_mul, Finset.sum_neg_distrib, neg_neg, Finset.sum_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring


def coordinateSeparatedWordSum {N : ℕ} (B K : RegularJointSpace N → Fin N → ℂ) (η τ ξ : ℝ) (F : RegularJointSpace N → ℂ)
    (g : (Fin N → ℝ) → ℂ) (n : ℕ) (x : ℂ × (Fin N → ℝ)) : ℂ :=
  ∑ w : TransportWord N n,
    transportAnalyticWord B
      K F n w (regularJointMap (actualPhysicalCoordinate η τ ξ) x) *
    transportAngularWord (actualBalancedInverseEntry η τ ξ) g n w x.2

theorem coordinateSeparatedWordSum_zero {N : ℕ} (B K : RegularJointSpace N → Fin N → ℂ) (η τ ξ : ℝ) (F : RegularJointSpace N → ℂ)
    (g : (Fin N → ℝ) → ℂ) (x : ℂ × (Fin N → ℝ)) :
    coordinateSeparatedWordSum B K η τ ξ F g 0 x = F (regularJointMap (actualPhysicalCoordinate η τ ξ) x) * g x.2 := by
  simp only [coordinateSeparatedWordSum, transportAnalyticWord, transportAngularWord,
    Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, pow_zero, one_nsmul]

theorem coordinateSeparatedWordSum_step {N : ℕ} (B K : RegularJointSpace N → Fin N → ℂ) (η τ ξ : ℝ)
    (F : RegularJointSpace N → ℂ) (g : (Fin N → ℝ) → ℂ)
    (x : ℂ × (Fin N → ℝ))
    (hχ : ∀ i, DifferentiableAt ℝ (actualPhysicalCoordinate η τ ξ i) x)
    (hB : AnalyticAt ℂ B
      (regularJointMap (actualPhysicalCoordinate η τ ξ) x))
    (hK : ∀ j, AnalyticAt ℂ (fun p : RegularJointSpace N => K p j)
      (regularJointMap (actualPhysicalCoordinate η τ ξ) x))
    (hF : AnalyticAt ℂ F (regularJointMap (actualPhysicalCoordinate η τ ξ) x))
    (hA : ∀ i j, ContDiffAt ℝ ∞ (actualBalancedInverseEntry η τ ξ i j) x.2)
    (hg : ContDiffAt ℝ ∞ g x.2)
    (hdet : actualCoordinateDeterminant η τ ξ x ≠ 0)
    (hV : ∀ i, coordinateAngularVelocity B η τ ξ i x =
      -∑ j, actualBalancedInverseEntry η τ ξ i j x.2 *
        K (regularJointMap (actualPhysicalCoordinate η τ ξ) x) j)
    (n : ℕ) :
    coordinateTransportAmplitude B η τ ξ (coordinateSeparatedWordSum B K η τ ξ F g n) x =
      coordinateSeparatedWordSum B K η τ ξ F g (n + 1) x := by
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
    actualTimeDirection (coordinateRegularField B η τ ξ)
    (fun y => ∑ w : TransportWord N n, transportAnalyticWord B K F n w
      (regularJointMap (actualPhysicalCoordinate η τ ξ) y) * transportAngularWord A g n w y.2) x = _
  rw [regularTransportAmplitude_sum _ _ _ _ _ _ hdiff hdet]
  have hs (w : TransportWord N n) := coordinateTransport_separated_product B K η τ ξ
    (transportAnalyticWord B K F n w) (transportAngularWord A g n w) x hχ hB.differentiableAt
    (hFw w).differentiableAt ((hgw w).differentiableAt (by simp)) hdet hV
  change (∑ w : TransportWord N n, coordinateTransportAmplitude B η τ ξ
    (fun y => transportAnalyticWord B K F n w
      (regularJointMap (actualPhysicalCoordinate η τ ξ) y) * transportAngularWord A g n w y.2) x) = _
  simp_rw [hs]
  rw [coordinateSeparatedWordSum, transportWord_sum_succ]
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

theorem coordinateTransportDescendant_eq_separated_words {N : ℕ} (B K : RegularJointSpace N → Fin N → ℂ) (η τ ξ : ℝ)
    (F : RegularJointSpace N → ℂ) (g : (Fin N → ℝ) → ℂ)
    (hA : ∀ i j : Fin N, ContDiff ℝ ∞ (actualBalancedInverseEntry η τ ξ i j))
    (hg : ContDiff ℝ ∞ g)
    (x : ℂ × (Fin N → ℝ))
    (hχ : ∀ i, ContDiffAt ℝ 2 (actualPhysicalCoordinate η τ ξ i) x)
    (hB : AnalyticAt ℂ B
      (regularJointMap (actualPhysicalCoordinate η τ ξ) x))
    (hK : ∀ j, AnalyticAt ℂ (fun p : RegularJointSpace N => K p j)
      (regularJointMap (actualPhysicalCoordinate η τ ξ) x))
    (hF : AnalyticAt ℂ F (regularJointMap (actualPhysicalCoordinate η τ ξ) x))
    (hdet : actualCoordinateDeterminant η τ ξ x ≠ 0)
    (hV : ∀ᶠ y in 𝓝 x, ∀ i, coordinateAngularVelocity B η τ ξ i y =
      -∑ j, actualBalancedInverseEntry η τ ξ i j y.2 *
        K (regularJointMap (actualPhysicalCoordinate η τ ξ) y) j)
    (n : ℕ) :
    coordinateTransportDescendant B η τ ξ
      (fun y => F (regularJointMap (actualPhysicalCoordinate η τ ξ) y) * g y.2) n x =
      coordinateSeparatedWordSum B K η τ ξ F g n x := by
  induction n generalizing x with
  | zero => exact (coordinateSeparatedWordSum_zero B K η τ ξ F g x).symm
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
        (fun p : RegularJointSpace N => K p j)
        (regularJointMap (actualPhysicalCoordinate η τ ξ) y) :=
      Filter.eventually_all.mpr (fun j => hm.eventually (hK j).eventually_analyticAt)
    have hFnear := hm.eventually hF.eventually_analyticAt
    have hVnear := eventually_eventually_nhds.mpr hV
    have heq : coordinateTransportDescendant B η τ ξ
        (fun y => F (regularJointMap (actualPhysicalCoordinate η τ ξ) y) * g y.2) n =ᶠ[𝓝 x]
        coordinateSeparatedWordSum B K η τ ξ F g n := by
      filter_upwards [hχnear, hdnear, hBnear, hKnear, hFnear, hVnear] with y hχy hdy hBy hKy hFy hVy
      exact ih y hχy hBy hKy hFy hdy hVy
    change regularTransportAmplitude (actualPhysicalCoordinate η τ ξ) actualAngularDirection
      actualTimeDirection (coordinateRegularField B η τ ξ)
      (coordinateTransportDescendant B η τ ξ
        (fun y => F (regularJointMap (actualPhysicalCoordinate η τ ξ) y) * g y.2) n) x = _
    rw [regularTransportAmplitude_congr_germ _ _ _ _ _ _ _ heq]
    exact coordinateSeparatedWordSum_step B K η τ ξ F g x hχd hB hK hF
      (fun i j => (hA i j).contDiffAt) hg.contDiffAt hdet hV.self_of_nhds n


end IsingBulk.AnisoF002.Isotropic
