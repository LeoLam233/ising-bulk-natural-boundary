import IsingBulk.AnisoF002.C03.RegularCollisionNumerator

/-!
# Exact analytic blow-up of the actual collision phase

The temperature is s²t and each complex angle is sx.  Both the cosine
zero and the phase difference are filled by actual divided differences.
Thus the original phase difference has an exact s² factor, and the
remaining function is jointly analytic at s=0.  No asymptotic polynomial
is substituted for the physical dispersion.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set Filter IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators

theorem analyticAt_dslope_center {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) :
    AnalyticAt ℂ (dslope f z) z := by
  let U : Set ℂ := {w | AnalyticAt ℂ f w}
  have hU : U ∈ 𝓝 z := hf.eventually_analyticAt
  have hd : DifferentiableOn ℂ f U := fun w hw => hw.differentiableAt.differentiableWithinAt
  exact ((Complex.differentiableOn_dslope hU).mpr hd).analyticAt hU

theorem one_sub_cos_filled (z : ℂ) :
    1 - Complex.cos z = z ^ 2 / 2 * complexSinc (z / 2) ^ 2 := by
  have hc := Complex.cos_two_mul_eq_one_sub (z / 2)
  have hs := complexSinc_mul (z / 2)
  rw [show 2 * (z / 2) = z by ring] at hc
  rw [← hs] at hc
  linear_combination -hc

def collisionBlowupIncrement (a : ℂ → ℂ) (x : ℂ) (p : ℂ × ℂ) : ℂ :=
  p.2 + a (p.1 ^ 2 * p.2) * x ^ 2 / 2 * complexSinc (p.1 * x / 2) ^ 2

def collisionBlowupPhase (b : ℝ) (a : ℂ → ℂ) (x : ℂ) (p : ℂ × ℂ) : ℂ :=
  dslope upperEdgePhase (b : ℂ) ((b : ℂ) + p.1 ^ 2 * collisionBlowupIncrement a x p) *
    collisionBlowupIncrement a x p

def collisionBlowupTotal {N : ℕ} (b : ℝ) (a : ℂ → ℂ) (x : Fin N → ℂ)
    (p : ℂ × ℂ) : ℂ := ∑ i, collisionBlowupPhase b a (x i) p

theorem collisionBlowupPhase_exact (b : ℝ) (a : ℂ → ℂ) (x s t : ℂ) :
    regularComplexPhase b a (s ^ 2 * t, s * x) - upperEdgePhase (b : ℂ) =
      s ^ 2 * collisionBlowupPhase b a x (s, t) := by
  have hW : (b : ℂ) + s ^ 2 * t + a (s ^ 2 * t) * (1 - Complex.cos (s * x)) =
      (b : ℂ) + s ^ 2 * collisionBlowupIncrement a x (s, t) := by
    rw [one_sub_cos_filled]
    unfold collisionBlowupIncrement
    ring
  have hs := sub_smul_dslope upperEdgePhase (b : ℂ)
    ((b : ℂ) + s ^ 2 * collisionBlowupIncrement a x (s, t))
  change upperEdgePhase ((b : ℂ) + s ^ 2 * t + a (s ^ 2 * t) *
    (1 - Complex.cos (s * x))) - upperEdgePhase (b : ℂ) = _
  rw [hW]
  simpa only [add_sub_cancel_left, smul_eq_mul, collisionBlowupPhase,
    mul_assoc, mul_comm (collisionBlowupIncrement a x (s, t))] using hs.symm

theorem collisionBlowupTotal_exact {N : ℕ} (b : ℝ) (a : ℂ → ℂ)
    (x : Fin N → ℂ) (s t : ℂ) :
    edgeJointTotalPhase (affineEdgeCenter b) a (s ^ 2 * t, fun i => s * x i) -
      (N : ℂ) * upperEdgePhase (b : ℂ) = s ^ 2 * collisionBlowupTotal b a x (s, t) := by
  have he := congrArg (fun f : (Fin N → ℂ) => ∑ i, f i)
    (funext fun i => collisionBlowupPhase_exact b a (x i) s t)
  simpa only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, collisionBlowupTotal,
    edgeJointTotalPhase, regularComplexPhase] using he

theorem collisionBlowupIncrement_analytic {a : ℂ → ℂ} (ha : AnalyticAt ℂ a 0)
    (x t : ℂ) : AnalyticAt ℂ (collisionBlowupIncrement a x) (0, t) := by
  have hs : AnalyticAt ℂ (fun p : ℂ × ℂ => p.1 ^ 2 * p.2) (0, t) :=
    (analyticAt_fst.pow 2).mul analyticAt_snd
  have hA := ha.comp_of_eq hs (by simp)
  have hsin : AnalyticAt ℂ (fun p : ℂ × ℂ => complexSinc (p.1 * x / 2)) (0, t) :=
    (complexSinc_analyticAt _).comp ((analyticAt_fst.mul analyticAt_const).div_const)
  exact analyticAt_snd.add (((hA.mul analyticAt_const).div_const).mul (hsin.pow 2))

theorem collisionBlowupPhase_analytic {b : ℝ} {a : ℂ → ℂ}
    (hb : |b| < 1) (ha : AnalyticAt ℂ a 0) (x t : ℂ) :
    AnalyticAt ℂ (collisionBlowupPhase b a x) (0, t) := by
  have hin := collisionBlowupIncrement_analytic ha x t
  have hW : 1 - (b : ℂ) ^ 2 ∈ Complex.slitPlane :=
    edge_discriminant_slit (Or.inr ⟨rfl, hb⟩)
  have hd := analyticAt_dslope_center (upperEdgePhase_analyticAt hW)
  exact ((hd.comp_of_eq (analyticAt_const.add ((analyticAt_fst.pow 2).mul hin))
    (by simp)).mul hin)

theorem collisionBlowupTotal_analytic {N : ℕ} {b : ℝ} {a : ℂ → ℂ}
    (hb : |b| < 1) (ha : AnalyticAt ℂ a 0) (x : Fin N → ℂ) (t : ℂ) :
    AnalyticAt ℂ (collisionBlowupTotal b a x) (0, t) :=
  Finset.univ.analyticAt_fun_sum fun i _ => collisionBlowupPhase_analytic hb ha (x i) t

theorem collisionBlowupTotal_center {N : ℕ} (b : ℝ) (a : ℂ → ℂ)
    (x : Fin N → ℂ) (t : ℂ) :
    collisionBlowupTotal b a x (0, t) =
      deriv upperEdgePhase (b : ℂ) * ((N : ℂ) * t + a 0 / 2 * ∑ i, x i ^ 2) := by
  simp only [collisionBlowupTotal, collisionBlowupPhase, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    zero_mul, add_zero, dslope_same, collisionBlowupIncrement, zero_div,
    complexSinc_zero, one_pow, mul_one]
  simp only [Finset.mul_sum, Finset.sum_add_distrib, mul_add, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro i _
    ring

theorem upperEdgePhase_deriv_ne_zero {b : ℝ} (hb : |b| < 1) :
    deriv upperEdgePhase (b : ℂ) ≠ 0 := by
  have hreg : upperEdgeRegion (b : ℂ) := Or.inr ⟨rfl, hb⟩
  have hd := upperEdgeRoot_pair_denominator hreg hreg
  have hs := exp_sinh_denominator (upperEdgePhase (b : ℂ))
  rw [upperEdgePhase_exp_neg] at hs
  have hsn : Complex.sinh (upperEdgePhase (b : ℂ)) ≠ 0 := by
    intro he
    rw [he, mul_zero] at hs
    exact hd (by simpa only [pow_two] using hs)
  rw [(upperEdgePhase_hasDerivAt (edge_discriminant_slit hreg)).deriv]
  exact one_div_ne_zero hsn

theorem collisionBlowupTotal_center_ne_zero {N : ℕ} (hN : 0 < N) {b : ℝ} {a : ℂ → ℂ}
    (hb : |b| < 1) (ha : 0 < (a 0).im) (x : Fin N → ℝ) :
    collisionBlowupTotal b a (complexAngles x) (0, Complex.I) ≠ 0 := by
  rw [collisionBlowupTotal_center]
  apply mul_ne_zero (upperEdgePhase_deriv_ne_zero hb)
  have hQ : 0 ≤ ∑ i, (x i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have him : 0 < ((N : ℂ) * Complex.I + a 0 / 2 * ∑ i, (complexAngles x i) ^ 2).im := by
    have hcast : (∑ i, (complexAngles x i) ^ 2) = ((∑ i, (x i) ^ 2 : ℝ) : ℂ) := by
      simp only [complexAngles, Complex.ofReal_sum, Complex.ofReal_pow]
    rw [hcast]
    simp only [Complex.add_im, Complex.mul_im, Complex.natCast_re, Complex.I_im,
      mul_one, Complex.natCast_im, Complex.I_re, mul_zero, add_zero, Complex.div_ofNat_im,
      Complex.ofReal_re, Complex.ofReal_im]
    positivity
  intro he
  rw [he, Complex.zero_im] at him
  exact lt_irrefl _ him

end
end IsingBulk.AnisoF002.RegularTail.C03
