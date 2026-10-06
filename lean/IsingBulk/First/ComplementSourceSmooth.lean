import IsingBulk.First.ComplementSourceAnalytic

/-! Local joint real smoothness of the literal source regular amplitude.
Only the original inactive rational denominators are required nonzero. -/
namespace IsingBulk.First
noncomputable section
open scoped BigOperators ContDiff
attribute [local fun_prop] source_complexOfReal_contDiff

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem anglePoint_joint_contDiff : ContDiff ℝ ∞ (fun p : ℝ × ℝ => anglePoint p.1 p.2) := by
  unfold anglePoint circleMap
  fun_prop

attribute [local fun_prop] anglePoint_joint_contDiff

theorem anglePoint_ne_zero_of_radius {r : ℝ} (hr : r ≠ 0) (θ : ℝ) :
    anglePoint r θ ≠ 0 := by
  simp only [anglePoint, circleMap, zero_add]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hr) (Complex.exp_ne_zero _)

theorem coordinateProduct_contDiffAt {N : ℕ} {x : P → Fin N → ℂ} {p : P}
    (hx : ∀ i, ContDiffAt ℝ ∞ (fun q => x q i) p) :
    ContDiffAt ℝ ∞ (fun q => coordinateProduct (x q)) p := by
  unfold coordinateProduct
  fun_prop

theorem sourceFactorDenominator_contDiffAt {N : ℕ} {x y : P → Fin N → ℂ}
    {s : P → ℂ} {p : P} (hx : ∀ i, ContDiffAt ℝ ∞ (fun q => x q i) p)
    (hy : ∀ i, ContDiffAt ℝ ∞ (fun q => y q i) p) (hs : ContDiffAt ℝ ∞ s p)
    (hx0 : ∀ i, x p i ≠ 0) (hy0 : ∀ i, y p i ≠ 0) (hs0 : s p ≠ 0)
    (f : SingularFactorIndex N) :
    ContDiffAt ℝ ∞ (fun q => sourceFactorDenominator (s q) (x q) (y q) f) p := by
  rcases f with b | (⟨b, i, j⟩ | i)
  · cases b <;> exact contDiffAt_const.sub (coordinateProduct_contDiffAt (by assumption))
  · cases b <;> simp only [sourceFactorDenominator] <;> split
    · exact contDiffAt_const.sub ((hx i).mul (hx j))
    · exact contDiffAt_const
    · exact contDiffAt_const.sub ((hy i).mul (hy j))
    · exact contDiffAt_const
  · exact ((hs.add (hs.inv hs0)).sub (((hx i).add ((hx i).inv (hx0 i))).div_const 2)).sub
      (((hy i).add ((hy i).inv (hy0 i))).div_const 2)

theorem sourceDoubleNumerator_contDiffAt {N : ℕ} {x y : P → Fin N → ℂ} {p : P}
    (hx : ∀ i, ContDiffAt ℝ ∞ (fun q => x q i) p)
    (hy : ∀ i, ContDiffAt ℝ ∞ (fun q => y q i) p)
    (hx0 : ∀ i, x p i ≠ 0) (hy0 : ∀ i, y p i ≠ 0) :
    ContDiffAt ℝ ∞ (fun q => sourceDoubleNumerator (x q) (y q)) p := by
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
  exact (((hX.inv hX0).add (hY.inv hY0)).mul hPX).mul hPY

/-- A fixed smooth angular weight is retained as a real weight. The radius,
complex temperature, and all real angles vary jointly in this theorem. -/
theorem localizedRegularAmplitude_joint_contDiffAt {N : ℕ}
    (w : DoubleAngularVector N → ℝ) (hw : ContDiff ℝ ∞ w)
    (J : Finset (SingularFactorIndex N)) (r : ℝ) (s : ℂ) (u : DoubleAngularVector N)
    (hr : r ≠ 0) (hs : s ≠ 0)
    (hden : ∀ f ∈ Jᶜ, sourceFactorDenominator s (angleTuple r u.1) (angleTuple r u.2) f ≠ 0) :
    ContDiffAt ℝ ∞ (fun q : (ℝ × ℂ) × DoubleAngularVector N =>
      localizedRegularAmplitude q.1.1 q.1.2 w J q.2) ((r,s),u) := by
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
  have hnum := sourceDoubleNumerator_contDiffAt hx hy hx0 hy0
  have hprod : ContDiffAt ℝ ∞ (fun q : (ℝ × ℂ) × DoubleAngularVector N =>
      ∏ f ∈ Jᶜ, (sourceFactorDenominator q.1.2 (x q) (y q) f)⁻¹) ((r,s),u) := by
    apply contDiffAt_prod
    intro f hf
    exact (sourceFactorDenominator_contDiffAt hx hy contDiffAt_fst.snd hx0 hy0 hs f).inv
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
