import IsingBulk.First.OnsiteFactorization
import IsingBulk.First.ComplementSourceSmooth
import IsingBulk.First.ComplementSourceAnalytic

/-! Joint real smoothness and complex parameter analyticity of the literal
onsite regular amplitude, with the global product poles absent. -/
namespace IsingBulk.First
noncomputable section
open scoped BigOperators ContDiff
attribute [local fun_prop] source_complexOfReal_contDiff anglePoint_joint_contDiff
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem onsiteFactorDenominator_contDiffAt {N : ℕ} {x y : P → Fin N → ℂ}
    {s : P → ℂ} {p : P} (hx : ∀ i, ContDiffAt ℝ ∞ (fun q => x q i) p)
    (hy : ∀ i, ContDiffAt ℝ ∞ (fun q => y q i) p) (hs : ContDiffAt ℝ ∞ s p)
    (hx0 : ∀ i, x p i ≠ 0) (hy0 : ∀ i, y p i ≠ 0) (hs0 : s p ≠ 0)
    (f : SingularFactorIndex N) :
    ContDiffAt ℝ ∞ (fun q => onsiteFactorDenominator (s q) (x q) (y q) f) p := by
  cases f with
  | inl b => exact contDiffAt_const
  | inr f => exact sourceFactorDenominator_contDiffAt hx hy hs hx0 hy0 hs0 (.inr f)

theorem sourceOnsiteNumerator_contDiffAt {N : ℕ} {x y : P → Fin N → ℂ} {p : P}
    (hx : ∀ i, ContDiffAt ℝ ∞ (fun q => x q i) p)
    (hy : ∀ i, ContDiffAt ℝ ∞ (fun q => y q i) p)
    (hx0 : ∀ i, x p i ≠ 0) (hy0 : ∀ i, y p i ≠ 0) :
    ContDiffAt ℝ ∞ (fun q => sourceOnsiteNumerator (x q) (y q)) p := by
  have hX := coordinateProduct_contDiffAt hx
  have hY := coordinateProduct_contDiffAt hy
  have hX0 : coordinateProduct (x p) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hx0 i)
  have hY0 : coordinateProduct (y p) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hy0 i)
  have hPX : ContDiffAt ℝ ∞ (fun q => sourcePairNumerator (x q)) p := by
    unfold sourcePairNumerator
    fun_prop
  have hPY : ContDiffAt ℝ ∞ (fun q => sourcePairNumerator (y q)) p := by
    unfold sourcePairNumerator
    fun_prop
  exact (((hX.mul hY).inv (mul_ne_zero hX0 hY0)).mul hPX).mul hPY

theorem onsiteFactorDenominator_analyticAt {N : ℕ} (x y : Fin N → ℂ)
    (f : SingularFactorIndex N) {s : ℂ} (hs : s ≠ 0) :
    AnalyticAt ℂ (fun z => onsiteFactorDenominator z x y f) s := by
  cases f with
  | inl b => exact analyticAt_const
  | inr f => exact sourceFactorDenominator_analyticAt x y (.inr f) hs

theorem onsiteRegularAmplitude_analyticAt {N : ℕ} (r : ℝ)
    (w : DoubleAngularVector N → ℝ) (J : Finset (SingularFactorIndex N))
    (u : DoubleAngularVector N) {s : ℂ} (hs : s ≠ 0)
    (hden : ∀ f ∈ Jᶜ, onsiteFactorDenominator s (angleTuple r u.1) (angleTuple r u.2) f ≠ 0) :
    AnalyticAt ℂ (fun z => onsiteRegularAmplitude r z w J u) s := by
  have hp : AnalyticAt ℂ (fun z => ∏ f ∈ Jᶜ,
      (onsiteFactorDenominator z (angleTuple r u.1) (angleTuple r u.2) f)⁻¹) s := by
    apply Finset.analyticAt_fun_prod
    intro f hf
    exact (onsiteFactorDenominator_analyticAt _ _ f hs).inv (hden f hf)
  exact (analyticAt_const.mul hp).mul analyticAt_const

/-- A fixed smooth angular weight is retained as a real weight. The radius,
complex temperature, and all real angles vary jointly in this theorem. -/
theorem onsiteRegularAmplitude_joint_contDiffAt {N : ℕ}
    (w : DoubleAngularVector N → ℝ) (hw : ContDiff ℝ ∞ w)
    (J : Finset (SingularFactorIndex N)) (r : ℝ) (s : ℂ) (u : DoubleAngularVector N)
    (hr : r ≠ 0) (hs : s ≠ 0)
    (hden : ∀ f ∈ Jᶜ, onsiteFactorDenominator s (angleTuple r u.1) (angleTuple r u.2) f ≠ 0) :
    ContDiffAt ℝ ∞ (fun q : (ℝ × ℂ) × DoubleAngularVector N =>
      onsiteRegularAmplitude q.1.1 q.1.2 w J q.2) ((r,s),u) := by
  let x : (ℝ × ℂ) × DoubleAngularVector N → Fin N → ℂ :=
    fun q => angleTuple q.1.1 q.2.1
  let y : (ℝ × ℂ) × DoubleAngularVector N → Fin N → ℂ :=
    fun q => angleTuple q.1.1 q.2.2
  have hx (i) : ContDiffAt ℝ ∞ (fun q => x q i) ((r,s),u) := by
    change ContDiffAt ℝ ∞ (fun q : (ℝ × ℂ) × DoubleAngularVector N =>
      anglePoint q.1.1 (q.2.1 i)) ((r,s),u)
    exact anglePoint_joint_contDiff.contDiffAt.comp ((r,s),u)
      (show ContDiffAt ℝ ∞ (fun q : (ℝ × ℂ) × DoubleAngularVector N =>
        (q.1.1, q.2.1 i)) ((r,s),u) by fun_prop)
  have hy (i) : ContDiffAt ℝ ∞ (fun q => y q i) ((r,s),u) := by
    change ContDiffAt ℝ ∞ (fun q : (ℝ × ℂ) × DoubleAngularVector N =>
      anglePoint q.1.1 (q.2.2 i)) ((r,s),u)
    exact anglePoint_joint_contDiff.contDiffAt.comp ((r,s),u)
      (show ContDiffAt ℝ ∞ (fun q : (ℝ × ℂ) × DoubleAngularVector N =>
        (q.1.1, q.2.2 i)) ((r,s),u) by fun_prop)
  have hx0 (i) : x ((r,s),u) i ≠ 0 := anglePoint_ne_zero_of_radius hr _
  have hy0 (i) : y ((r,s),u) i ≠ 0 := anglePoint_ne_zero_of_radius hr _
  have hnum := sourceOnsiteNumerator_contDiffAt hx hy hx0 hy0
  have hprod : ContDiffAt ℝ ∞ (fun q : (ℝ × ℂ) × DoubleAngularVector N =>
      ∏ f ∈ Jᶜ, (onsiteFactorDenominator q.1.2 (x q) (y q) f)⁻¹) ((r,s),u) := by
    apply contDiffAt_prod
    intro f hf
    exact (onsiteFactorDenominator_contDiffAt hx hy contDiffAt_fst.snd hx0 hy0 hs f).inv
      (hden f hf)
  have hJx : ContDiffAt ℝ ∞ (fun q : (ℝ × ℂ) × DoubleAngularVector N =>
      angleProductJacobian q.1.1 q.2.1) ((r,s),u) := by
    unfold angleProductJacobian angleJacobian
    fun_prop
  have hJy : ContDiffAt ℝ ∞ (fun q : (ℝ × ℂ) × DoubleAngularVector N =>
      angleProductJacobian q.1.1 q.2.2) ((r,s),u) := by
    unfold angleProductJacobian angleJacobian
    fun_prop
  have hwc : ContDiffAt ℝ ∞ (fun q : (ℝ × ℂ) × DoubleAngularVector N => (w q.2 : ℂ))
      ((r,s),u) := by fun_prop
  exact (((((hwc.mul hJy).mul hJx).mul hnum).mul hprod).mul contDiffAt_const)


end
end IsingBulk.First
