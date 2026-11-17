import IsingBulk.AnisoF002.C03.IsotropicTrigonometricSecants
import IsingBulk.AnisoF002.Isotropic.InverseCurvature

/-!
# Joint analyticity of the actual inverse secants

The functions are the `dslope` values of the actual joint inverse and of
its actual coordinate derivative. The original unsquared dispersion fills
the diagonal by analytic trigonometric quotients. No new inverse, derivative,
secant, or physical premise is substituted for the existing one.
-/

noncomputable section

set_option maxHeartbeats 800000

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology
open Filter Set

def jointFirstSecant (U : ℂ × ℂ → ℂ) (q : ℂ × ℂ × ℂ) : ℂ :=
  dslope (fun v => U (q.1, v)) q.2.2 q.2.1

def jointSecondSecant (U : ℂ × ℂ → ℂ) (q : ℂ × ℂ × ℂ) : ℂ :=
  dslope (deriv (fun v => U (q.1, v))) q.2.2 q.2.1

def inverseSecantDenominator (U : ℂ × ℂ → ℂ) (q : ℂ × ℂ × ℂ) : ℂ :=
  minusCosineSecant (q.2.1 - U (q.1, q.2.1)) (q.2.2 - U (q.1, q.2.2)) -
    minusCosineSecant (U (q.1, q.2.1)) (U (q.1, q.2.2))

def inverseFirstSecantQuotient (U : ℂ × ℂ → ℂ) (q : ℂ × ℂ × ℂ) : ℂ :=
  minusCosineSecant (q.2.1 - U (q.1, q.2.1)) (q.2.2 - U (q.1, q.2.2)) /
    inverseSecantDenominator U q

theorem inverseSecantDenominator_analyticAt (U : ℂ × ℂ → ℂ) (q : ℂ × ℂ × ℂ)
    (ha : AnalyticAt ℂ U (q.1, q.2.1)) (hb : AnalyticAt ℂ U (q.1, q.2.2)) :
    AnalyticAt ℂ (inverseSecantDenominator U) q := by
  have hS : AnalyticAt ℂ (fun p : ℂ × ℂ × ℂ => p.1) q := analyticAt_fst
  have hA : AnalyticAt ℂ (fun p : ℂ × ℂ × ℂ => p.2.1) q :=
    analyticAt_fst.comp analyticAt_snd
  have hB : AnalyticAt ℂ (fun p : ℂ × ℂ × ℂ => p.2.2) q :=
    analyticAt_snd.comp analyticAt_snd
  have hUa := ha.comp (f := fun p : ℂ × ℂ × ℂ => (p.1, p.2.1)) (hS.prod hA)
  have hUb := hb.comp (f := fun p : ℂ × ℂ × ℂ => (p.1, p.2.2)) (hS.prod hB)
  have hp : AnalyticAt ℂ
      (fun p : ℂ × ℂ × ℂ => minusCosineSecant
        (p.2.1 - U (p.1, p.2.1)) (p.2.2 - U (p.1, p.2.2))) q :=
    (minusCosineSecant_analyticAt
      (q.2.1 - U (q.1, q.2.1), q.2.2 - U (q.1, q.2.2))).comp
      (f := fun p : ℂ × ℂ × ℂ =>
        (p.2.1 - U (p.1, p.2.1), p.2.2 - U (p.1, p.2.2)))
      ((hA.sub hUa).prod (hB.sub hUb))
  have hw : AnalyticAt ℂ
      (fun p : ℂ × ℂ × ℂ => minusCosineSecant
        (U (p.1, p.2.1)) (U (p.1, p.2.2))) q :=
    (minusCosineSecant_analyticAt (U (q.1, q.2.1), U (q.1, q.2.2))).comp
      (f := fun p : ℂ × ℂ × ℂ => (U (p.1, p.2.1), U (p.1, p.2.2)))
      (hUa.prod hUb)
  exact hp.sub hw

theorem inverseFirstSecantQuotient_analyticAt (U : ℂ × ℂ → ℂ) (q : ℂ × ℂ × ℂ)
    (ha : AnalyticAt ℂ U (q.1, q.2.1)) (hb : AnalyticAt ℂ U (q.1, q.2.2))
    (hK : inverseSecantDenominator U q ≠ 0) :
    AnalyticAt ℂ (inverseFirstSecantQuotient U) q := by
  have hS : AnalyticAt ℂ (fun p : ℂ × ℂ × ℂ => p.1) q := analyticAt_fst
  have hA : AnalyticAt ℂ (fun p : ℂ × ℂ × ℂ => p.2.1) q :=
    analyticAt_fst.comp analyticAt_snd
  have hB : AnalyticAt ℂ (fun p : ℂ × ℂ × ℂ => p.2.2) q :=
    analyticAt_snd.comp analyticAt_snd
  have hUa := ha.comp (f := fun p : ℂ × ℂ × ℂ => (p.1, p.2.1)) (hS.prod hA)
  have hUb := hb.comp (f := fun p : ℂ × ℂ × ℂ => (p.1, p.2.2)) (hS.prod hB)
  exact ((minusCosineSecant_analyticAt _).comp
    ((hA.sub hUa).prod (hB.sub hUb))).div
      (inverseSecantDenominator_analyticAt U q ha hb) hK

/-- Difference of the original dispersion equations, before any division. -/
theorem inverse_first_secant_difference (S a b wa wb : ℂ)
    (ha : Complex.cos wa + Complex.cos (a - wa) = S)
    (hb : Complex.cos wb + Complex.cos (b - wb) = S) :
    (wa - wb) *
        (minusCosineSecant (a - wa) (b - wb) - minusCosineSecant wa wb) =
      (a - b) * minusCosineSecant (a - wa) (b - wb) := by
  have hw := minusCosineSecant_difference wa wb
  have hp := minusCosineSecant_difference (a - wa) (b - wb)
  linear_combination hw + hp + ha - hb

/-- The actual filled first secant equals the analytic local quotient;
the diagonal case uses the actual coordinate derivative. -/
theorem jointFirstSecant_eq_quotient (U : ℂ × ℂ → ℂ) (S a b : ℂ)
    (hUa : AnalyticAt ℂ U (S, a))
    (hdispa : ∀ᶠ q in 𝓝 (S, a),
      Complex.cos (U q) + Complex.cos (q.2 - U q) = q.1)
    (hdispb : Complex.cos (U (S, b)) + Complex.cos (b - U (S, b)) = S)
    (hK : inverseSecantDenominator U (S, a, b) ≠ 0) :
    jointFirstSecant U (S, a, b) = inverseFirstSecantQuotient U (S, a, b) := by
  by_cases hab : a = b
  · subst b
    have hden : Complex.sin (a - U (S, a)) - Complex.sin (U (S, a)) ≠ 0 := by
      simpa only [inverseSecantDenominator, minusCosineSecant_self] using hK
    have hd := joint_inverse_coordinate_derivative U S a hUa hdispa hden
    simpa only [jointFirstSecant, dslope_same, inverseFirstSecantQuotient,
      inverseSecantDenominator, minusCosineSecant_self] using hd.deriv
  · have hd := inverse_first_secant_difference S a b (U (S, a)) (U (S, b))
      hdispa.self_of_nhds hdispb
    have hab0 : a - b ≠ 0 := sub_ne_zero.mpr hab
    change (U (S, a) - U (S, b)) * inverseSecantDenominator U (S, a, b) =
      (a - b) * minusCosineSecant (a - U (S, a)) (b - U (S, b)) at hd
    dsimp only [jointFirstSecant, inverseFirstSecantQuotient]
    rw [dslope_of_ne _ hab, slope_def_field]
    apply (div_eq_div_iff hab0 hK).2
    simpa only [mul_comm] using hd

/-- Joint analyticity at arbitrary pairs, including every partial diagonal.
Only the actual inverse and its original local dispersion are assumed. -/
theorem jointFirstSecant_analyticAt (U : ℂ × ℂ → ℂ) (q : ℂ × ℂ × ℂ)
    (hUa : AnalyticAt ℂ U (q.1, q.2.1))
    (hUb : AnalyticAt ℂ U (q.1, q.2.2))
    (hdispa : ∀ᶠ z in 𝓝 (q.1, q.2.1),
      Complex.cos (U z) + Complex.cos (z.2 - U z) = z.1)
    (hdispb : ∀ᶠ z in 𝓝 (q.1, q.2.2),
      Complex.cos (U z) + Complex.cos (z.2 - U z) = z.1)
    (hDa : Complex.sin (q.2.1 - U (q.1, q.2.1)) - Complex.sin (U (q.1, q.2.1)) ≠ 0) :
    AnalyticAt ℂ (jointFirstSecant U) q := by
  have hS : AnalyticAt ℂ (fun p : ℂ × ℂ × ℂ => p.1) q := analyticAt_fst
  have hA : AnalyticAt ℂ (fun p : ℂ × ℂ × ℂ => p.2.1) q :=
    analyticAt_fst.comp analyticAt_snd
  have hB : AnalyticAt ℂ (fun p : ℂ × ℂ × ℂ => p.2.2) q :=
    analyticAt_snd.comp analyticAt_snd
  have hmapa := (hS.prod hA).continuousAt
  have hmapb := (hS.prod hB).continuousAt
  by_cases hab : q.2.1 = q.2.2
  · have hK : inverseSecantDenominator U q ≠ 0 := by
      simpa only [inverseSecantDenominator, ← hab, minusCosineSecant_self] using hDa
    have hKe := (inverseSecantDenominator_analyticAt U q hUa hUb).continuousAt.eventually_ne hK
    apply (inverseFirstSecantQuotient_analyticAt U q hUa hUb hK).congr
    filter_upwards [hmapa.eventually hUa.eventually_analyticAt,
      hmapa.eventually hdispa.eventually_nhds, hmapb.eventually hdispb, hKe]
      with p hpU hpd hpb hpK
    exact (jointFirstSecant_eq_quotient U p.1 p.2.1 p.2.2 hpU hpd hpb hpK).symm
  · have hquot : AnalyticAt ℂ
        (fun p : ℂ × ℂ × ℂ =>
          (U (p.1, p.2.1) - U (p.1, p.2.2)) / (p.2.1 - p.2.2)) q :=
      ((hUa.comp (f := fun p : ℂ × ℂ × ℂ => (p.1, p.2.1)) (hS.prod hA)).sub (hUb.comp (f := fun p : ℂ × ℂ × ℂ => (p.1, p.2.2)) (hS.prod hB))).div
        (hA.sub hB) (sub_ne_zero.mpr hab)
    apply hquot.congr
    filter_upwards [(hA.continuousAt.sub hB.continuousAt).eventually_ne (sub_ne_zero.mpr hab)]
      with p hp
    simp only [jointFirstSecant, dslope_of_ne _ (sub_ne_zero.mp hp), slope_def_field]

def jointInverseDenominator (U : ℂ × ℂ → ℂ) (q : ℂ × ℂ) : ℂ :=
  Complex.sin (q.2 - U q) - Complex.sin (U q)

theorem jointInverseDenominator_analyticAt (U : ℂ × ℂ → ℂ) (q : ℂ × ℂ)
    (hU : AnalyticAt ℂ U q) : AnalyticAt ℂ (jointInverseDenominator U) q :=
  (Complex.analyticAt_sin.comp (analyticAt_snd.sub hU)).sub
    (Complex.analyticAt_sin.comp hU)

def inverseSecondSecantQuotient (U : ℂ × ℂ → ℂ) (q : ℂ × ℂ × ℂ) : ℂ :=
  (Complex.sin (q.2.2 - U (q.1, q.2.2)) * jointFirstSecant U q *
      sineSecant (U (q.1, q.2.1)) (U (q.1, q.2.2)) -
    Complex.sin (U (q.1, q.2.2)) * (1 - jointFirstSecant U q) *
      sineSecant (q.2.1 - U (q.1, q.2.1)) (q.2.2 - U (q.1, q.2.2))) /
    (jointInverseDenominator U (q.1, q.2.1) *
      jointInverseDenominator U (q.1, q.2.2))

/-- Exact difference of the two derivative quotients. The secant equality
in the hypothesis is an algebraic input here, and is discharged by the
actual `dslope` identity in the application below. -/
theorem inverse_derivative_difference (a b wa wb e : ℂ)
    (he : (a - b) * e = wa - wb)
    (hDa : Complex.sin (a - wa) - Complex.sin wa ≠ 0)
    (hDb : Complex.sin (b - wb) - Complex.sin wb ≠ 0) :
    Complex.sin (a - wa) / (Complex.sin (a - wa) - Complex.sin wa) -
        Complex.sin (b - wb) / (Complex.sin (b - wb) - Complex.sin wb) =
      (a - b) *
        ((Complex.sin (b - wb) * e * sineSecant wa wb -
          Complex.sin wb * (1 - e) * sineSecant (a - wa) (b - wb)) /
          ((Complex.sin (a - wa) - Complex.sin wa) *
            (Complex.sin (b - wb) - Complex.sin wb))) := by
  have hp : (a - b) * (1 - e) = (a - wa) - (b - wb) := by
    linear_combination -he
  calc
    _ = (Complex.sin (b - wb) * (Complex.sin wa - Complex.sin wb) -
          Complex.sin wb * (Complex.sin (a - wa) - Complex.sin (b - wb))) /
        ((Complex.sin (a - wa) - Complex.sin wa) *
          (Complex.sin (b - wb) - Complex.sin wb)) := by
      field_simp [hDa, hDb]
      ring
    _ = _ := by
      rw [← sineSecant_difference wa wb, ← sineSecant_difference (a - wa) (b - wb),
        ← he, ← hp]
      ring

theorem inverseSecondSecantQuotient_diagonal (U : ℂ × ℂ → ℂ) (S a : ℂ)
    (hU : AnalyticAt ℂ U (S, a))
    (hdisp : ∀ᶠ q in 𝓝 (S, a),
      Complex.cos (U q) + Complex.cos (q.2 - U q) = q.1)
    (hD : jointInverseDenominator U (S, a) ≠ 0) :
    inverseSecondSecantQuotient U (S, a, a) =
      inverseCurvature S (U (S, a)) (a - U (S, a)) := by
  have hd := joint_inverse_coordinate_derivative U S a hU hdisp hD
  have hn := inverse_curvature_numerator (U (S, a)) (a - U (S, a)) S
    hdisp.self_of_nhds
  dsimp only [inverseSecondSecantQuotient, jointFirstSecant]
  rw [dslope_same, hd.deriv]
  simp only [sineSecant_self]
  unfold inverseCurvature jointInverseDenominator at *
  rw [← hn]
  field_simp [hD]
  ring

/-- The actual filled second secant equals a jointly analytic quotient on
every regular inverse chart. Partial coincidences use its true second derivative. -/
theorem jointSecondSecant_eq_quotient (U : ℂ × ℂ → ℂ) (S a b : ℂ)
    (hUa : AnalyticAt ℂ U (S, a)) (hUb : AnalyticAt ℂ U (S, b))
    (hdispa : ∀ᶠ q in 𝓝 (S, a),
      Complex.cos (U q) + Complex.cos (q.2 - U q) = q.1)
    (hdispb : ∀ᶠ q in 𝓝 (S, b),
      Complex.cos (U q) + Complex.cos (q.2 - U q) = q.1)
    (hDa : jointInverseDenominator U (S, a) ≠ 0)
    (hDb : jointInverseDenominator U (S, b) ≠ 0) :
    jointSecondSecant U (S, a, b) = inverseSecondSecantQuotient U (S, a, b) := by
  by_cases hab : a = b
  · subst b
    rw [inverseSecondSecantQuotient_diagonal U S a hUa hdispa hDa]
    simpa only [jointSecondSecant, dslope_same] using
      (joint_inverse_coordinate_second_derivative U S a hUa hdispa hDa).deriv
  · have hda := joint_inverse_coordinate_derivative U S a hUa hdispa hDa
    have hdb := joint_inverse_coordinate_derivative U S b hUb hdispb hDb
    have he : (a - b) * jointFirstSecant U (S, a, b) = U (S, a) - U (S, b) := by
      simpa only [jointFirstSecant, smul_eq_mul] using
        sub_smul_dslope (fun z => U (S, z)) b a
    have hdiff := inverse_derivative_difference a b (U (S, a)) (U (S, b))
      (jointFirstSecant U (S, a, b)) he hDa hDb
    apply mul_left_cancel₀ (sub_ne_zero.mpr hab)
    calc
      (a - b) * jointSecondSecant U (S, a, b) =
          deriv (fun z => U (S, z)) a - deriv (fun z => U (S, z)) b := by
        simpa only [jointSecondSecant, smul_eq_mul] using
          sub_smul_dslope (deriv (fun z => U (S, z))) b a
      _ = _ := by
        rw [hda.deriv, hdb.deriv]
        exact hdiff

theorem inverseSecondSecantQuotient_analyticAt
    (U : ℂ × ℂ → ℂ) (q : ℂ × ℂ × ℂ)
    (hUa : AnalyticAt ℂ U (q.1, q.2.1))
    (hUb : AnalyticAt ℂ U (q.1, q.2.2))
    (he : AnalyticAt ℂ (jointFirstSecant U) q)
    (hDa : jointInverseDenominator U (q.1, q.2.1) ≠ 0)
    (hDb : jointInverseDenominator U (q.1, q.2.2) ≠ 0) :
    AnalyticAt ℂ (inverseSecondSecantQuotient U) q := by
  have hS : AnalyticAt ℂ (fun p : ℂ × ℂ × ℂ => p.1) q := analyticAt_fst
  have hA : AnalyticAt ℂ (fun p : ℂ × ℂ × ℂ => p.2.1) q :=
    analyticAt_fst.comp analyticAt_snd
  have hB : AnalyticAt ℂ (fun p : ℂ × ℂ × ℂ => p.2.2) q :=
    analyticAt_snd.comp analyticAt_snd
  have hwa := hUa.comp (f := fun p : ℂ × ℂ × ℂ => (p.1, p.2.1)) (hS.prod hA)
  have hwb := hUb.comp (f := fun p : ℂ × ℂ × ℂ => (p.1, p.2.2)) (hS.prod hB)
  have hpa := hA.sub hwa
  have hpb := hB.sub hwb
  have hn := (((Complex.analyticAt_sin.comp hpb).mul he).mul
    ((sineSecant_analyticAt _).comp (hwa.prod hwb))).sub
      (((Complex.analyticAt_sin.comp hwb).mul
        ((analyticAt_const : AnalyticAt ℂ (fun _ : ℂ × ℂ × ℂ => (1 : ℂ)) q).sub he)).mul
        ((sineSecant_analyticAt _).comp (hpa.prod hpb)))
  exact hn.div
    (((jointInverseDenominator_analyticAt U _ hUa).comp (f := fun p : ℂ × ℂ × ℂ => (p.1, p.2.1)) (hS.prod hA)).mul
      ((jointInverseDenominator_analyticAt U _ hUb).comp (f := fun p : ℂ × ℂ × ℂ => (p.1, p.2.2)) (hS.prod hB)))
    (mul_ne_zero hDa hDb)

/-- Full joint analyticity of the true derivative secant across all partial
diagonals. No analytic divided-difference assumption is used. -/
theorem jointSecondSecant_analyticAt (U : ℂ × ℂ → ℂ) (q : ℂ × ℂ × ℂ)
    (hUa : AnalyticAt ℂ U (q.1, q.2.1))
    (hUb : AnalyticAt ℂ U (q.1, q.2.2))
    (hdispa : ∀ᶠ z in 𝓝 (q.1, q.2.1),
      Complex.cos (U z) + Complex.cos (z.2 - U z) = z.1)
    (hdispb : ∀ᶠ z in 𝓝 (q.1, q.2.2),
      Complex.cos (U z) + Complex.cos (z.2 - U z) = z.1)
    (hDa : jointInverseDenominator U (q.1, q.2.1) ≠ 0)
    (hDb : jointInverseDenominator U (q.1, q.2.2) ≠ 0) :
    AnalyticAt ℂ (jointSecondSecant U) q := by
  have hS : AnalyticAt ℂ (fun p : ℂ × ℂ × ℂ => p.1) q := analyticAt_fst
  have hA : AnalyticAt ℂ (fun p : ℂ × ℂ × ℂ => p.2.1) q :=
    analyticAt_fst.comp analyticAt_snd
  have hB : AnalyticAt ℂ (fun p : ℂ × ℂ × ℂ => p.2.2) q :=
    analyticAt_snd.comp analyticAt_snd
  have hmapa := (hS.prod hA).continuousAt
  have hmapb := (hS.prod hB).continuousAt
  have he := jointFirstSecant_analyticAt U q hUa hUb hdispa hdispb hDa
  have hDae := ((jointInverseDenominator_analyticAt U _ hUa).comp (f := fun p : ℂ × ℂ × ℂ => (p.1, p.2.1)) (hS.prod hA)).continuousAt.eventually_ne hDa
  have hDbe := ((jointInverseDenominator_analyticAt U _ hUb).comp (f := fun p : ℂ × ℂ × ℂ => (p.1, p.2.2)) (hS.prod hB)).continuousAt.eventually_ne hDb
  apply (inverseSecondSecantQuotient_analyticAt U q hUa hUb he hDa hDb).congr
  filter_upwards [hmapa.eventually hUa.eventually_analyticAt,
    hmapb.eventually hUb.eventually_analyticAt,
    hmapa.eventually hdispa.eventually_nhds, hmapb.eventually hdispb.eventually_nhds,
    hDae, hDbe] with p hpa hpb hpda hpdb hpaD hpbD
  exact (jointSecondSecant_eq_quotient U p.1 p.2.1 p.2.2 hpa hpb hpda hpdb hpaD hpbD).symm

end IsingBulk.AnisoF002.Isotropic
