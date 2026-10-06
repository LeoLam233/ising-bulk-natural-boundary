import IsingBulk.First.WeightedResidue
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Compact angular integrability and continuity of genuine iterated integrals. -/
namespace IsingBulk.First
noncomputable section
open Set MeasureTheory
open scoped BigOperators

def angleBox (N : ℕ) : Set (Fin N → ℝ) := Icc (fun _ => 0) (fun _ => 2*Real.pi)

/-- Every stage is an ordinary integrable interval integral. -/
def AngleStagesIntegrable : (N : ℕ) → ((Fin N → ℝ) → ℂ) → Prop
  | 0, _ => True
  | n+1, f =>
      (∀ θ : Fin n → ℝ, IntervalIntegrable (fun u : ℝ => f (Fin.cons u θ)) volume 0 (2*Real.pi)) ∧
      AngleStagesIntegrable n (fun θ => ∫ u : ℝ in 0..2*Real.pi, f (Fin.cons u θ))

theorem continuous_angle_integral {P : Type*} [TopologicalSpace P]
    [FirstCountableTopology P] [LocallyCompactSpace P]
    (f : P → ℝ → ℂ) (hf : Continuous (Function.uncurry f)) :
    Continuous (fun p => ∫ u : ℝ in 0..2*Real.pi, f p u) := by
  have hc := continuous_parametric_integral_of_continuous (μ := volume) hf
    (s := Icc (0:ℝ) (2*Real.pi)) isCompact_Icc
  have he (p : P) : (∫ u : ℝ in 0..2*Real.pi, f p u) = ∫ u in Icc (0:ℝ) (2*Real.pi), f p u := by
    rw [intervalIntegral.integral_of_le Real.two_pi_pos.le, integral_Icc_eq_integral_Ioc]
  simpa only [he] using hc

theorem continuous_multiAngleIntegral (N : ℕ) {P : Type*} [TopologicalSpace P]
    [FirstCountableTopology P] [LocallyCompactSpace P]
    (f : P → (Fin N → ℝ) → ℂ) (hf : Continuous (Function.uncurry f)) :
    Continuous (fun p => multiAngleIntegral N (f p)) := by
  induction N with
  | zero =>
    exact hf.comp (continuous_id.prodMk continuous_const)
  | succ n ih =>
    let g : (P × (Fin n → ℝ)) → ℝ → ℂ := fun p u => f p.1 (Fin.cons u p.2)
    have hg : Continuous (Function.uncurry g) := by
      have hm : Continuous (fun p : (P × (Fin n → ℝ)) × ℝ =>
        (p.1.1, (Fin.cons p.2 p.1.2 : Fin (n+1) → ℝ))) := by fun_prop
      exact hf.comp hm
    have hgi := continuous_angle_integral g hg
    exact ih (fun p θ => ∫ u : ℝ in 0..2*Real.pi, f p (Fin.cons u θ)) hgi

theorem continuous_angle_stages (N : ℕ) (f : (Fin N → ℝ) → ℂ) (hf : Continuous f) :
    AngleStagesIntegrable N f := by
  induction N with
  | zero => trivial
  | succ n ih =>
    constructor
    · intro θ
      apply Continuous.intervalIntegrable
      apply hf.comp
      fun_prop
    · apply ih
      apply continuous_angle_integral
      apply hf.comp
      fun_prop

theorem continuous_angleBox_integrable {N : ℕ} (f : (Fin N → ℝ) → ℂ) (hf : Continuous f) :
    IntegrableOn f (angleBox N) :=
  hf.continuousOn.integrableOn_compact isCompact_Icc

theorem angleTuple_continuous {N : ℕ} (r : ℝ) : Continuous (angleTuple (N := N) r) := by
  unfold angleTuple anglePoint
  fun_prop

theorem angleProductJacobian_continuous {N : ℕ} (r : ℝ) :
    Continuous (angleProductJacobian (N := N) r) := by
  unfold angleProductJacobian angleJacobian anglePoint
  fun_prop

theorem anglePoint_norm {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) : ‖anglePoint r θ‖ = r := by
  simp [anglePoint, norm_circleMap_zero, abs_of_nonneg hr]

theorem dispersion_ne_zero_on_circle {N : ℕ} {r : ℝ} {s : ℂ}
    {y z : Fin N → ℂ} (h : ResidueAdmissible r s y z) {x : ℂ}
    (hx : ‖x‖ = r) (i : Fin N) : dispersion x (y i) s ≠ 0 := by
  have hx0 : x ≠ 0 := by intro he; simp [he] at hx; linarith [h.radius_pos]
  rw [dispersion_factorization hx0 (h.y_ne_zero i) (h.root_ne_zero i) (h.root_quadratic i)]
  apply div_ne_zero
  · apply mul_ne_zero
    · apply neg_ne_zero.mpr
      intro he
      have he' : x = z i := sub_eq_zero.mp he
      have hz := h.root_inside i
      rw [← he', hx] at hz
      exact lt_irrefl _ hz
    · exact exterior_root_ne_on_disk h.radius_lt_one hx.le (h.root_inside i) (h.root_ne_zero i)
  · exact mul_ne_zero (by norm_num) hx0

end
end IsingBulk.First
