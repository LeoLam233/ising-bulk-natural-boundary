import IsingBulk.Tail.CompactPairSlope
import IsingBulk.Tail.TwoRowDeterminant

/-! Exact midpoint geometry for the coupled extreme-coordinate coarea chart. -/
namespace IsingBulk.Tail
noncomputable section
open Set
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

def pairMidpoint {N : ℕ} (x : Fin N → ℝ) (i j : Fin N) : Fin N → ℝ :=
  x-((x i-x j)/2) • pairDirection i j

theorem pairMidpoint_equal {N : ℕ} (x : Fin N → ℝ) {i j : Fin N} (hij : i≠j) :
    pairMidpoint x i j i=pairMidpoint x i j j := by
  simp only [pairMidpoint,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,pairDirection,Pi.single_eq_same,
    Pi.single_eq_of_ne hij,Pi.single_eq_of_ne (Ne.symm hij)]
  ring

theorem pairMidpoint_recover {N : ℕ} (x : Fin N → ℝ) (i j : Fin N) :
    pairMidpoint x i j+((x i-x j)/2) • pairDirection i j=x := by
  exact sub_add_cancel x _

theorem pairMidpoint_path_mem {N : ℕ} (x : Fin N → ℝ) {i j : Fin N} (hij : i≠j)
    (horder : x i≤x j) {lo hi : ℝ} (hx : ∀ l, x l∈Icc lo hi)
    {t : ℝ} (ht : t∈Icc ((x i-x j)/2) 0) :
    ∀ l, (pairMidpoint x i j+t • pairDirection i j) l∈Icc lo hi := by
  intro l
  have hxi := hx i
  have hxj := hx j
  by_cases hli : l=i
  · subst l
    simp only [pairMidpoint,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,pairDirection,
      Pi.single_eq_same,Pi.single_eq_of_ne hij,sub_zero,mul_one]
    constructor <;> linarith [ht.1,ht.2,hxi.1,hxi.2,hxj.1,hxj.2]
  · by_cases hlj : l=j
    · subst l
      simp only [pairMidpoint,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,pairDirection,
        Pi.single_eq_same,Pi.single_eq_of_ne (Ne.symm hij),zero_sub,mul_neg,mul_one]
      constructor <;> linarith [ht.1,ht.2,hxi.1,hxi.2,hxj.1,hxj.2]
    · simpa [pairMidpoint,pairDirection,Pi.single_apply,hli,hlj] using hx l

/-- A two-row phase update retains every spectator coordinate, so equality of
its values fixes the spectators before the two-dimensional injectivity step. -/
def twoPhaseUpdate {N : ℕ} (F G : (Fin N → ℝ) → ℝ) (i j : Fin N)
    (x : Fin N → ℝ) : Fin N → ℝ :=
  fun l => if l=i then F x else if l=j then G x else x l

theorem twoPhaseUpdate_equal_data {N : ℕ} {F G : (Fin N → ℝ) → ℝ}
    {i j : Fin N} (hij : i≠j) {x y : Fin N → ℝ}
    (h : twoPhaseUpdate F G i j x=twoPhaseUpdate F G i j y) :
    F x=F y ∧ G x=G y ∧ ∀ l, l≠i → l≠j → x l=y l := by
  refine ⟨?_,?_,?_⟩
  · simpa [twoPhaseUpdate] using congrFun h i
  · simpa [twoPhaseUpdate,Ne.symm hij] using congrFun h j
  · intro l hli hlj
    simpa [twoPhaseUpdate,hli,hlj] using congrFun h l


def twoPhaseUpdateDeriv {N : ℕ} (F' G' : (Fin N → ℝ) →L[ℝ] ℝ) (i j : Fin N) :
    (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) :=
  ContinuousLinearMap.pi (fun l => if l=i then F' else if l=j then G' else ContinuousLinearMap.proj l)

theorem twoPhaseUpdate_hasFDerivAt {N : ℕ} {F G : (Fin N → ℝ) → ℝ}
    {F' G' : (Fin N → ℝ) →L[ℝ] ℝ} {x : Fin N → ℝ}
    (hF : HasFDerivAt F F' x) (hG : HasFDerivAt G G' x) (i j : Fin N) :
    HasFDerivAt (twoPhaseUpdate F G i j) (twoPhaseUpdateDeriv F' G' i j) x := by
  unfold twoPhaseUpdate twoPhaseUpdateDeriv
  rw [hasFDerivAt_pi]
  intro l
  by_cases hli : l=i
  · simpa [twoPhaseUpdate,twoPhaseUpdateDeriv,hli] using hF
  · by_cases hlj : l=j
    · have hji : j≠i := by simpa only [hlj] using hli
      simpa [twoPhaseUpdate,twoPhaseUpdateDeriv,hlj,hji] using hG
    · simp only [hli,hlj,ite_false]
      exact (ContinuousLinearMap.proj l : (Fin N → ℝ) →L[ℝ] ℝ).hasFDerivAt

theorem twoPhaseUpdateDeriv_det {N : ℕ} (F' G' : (Fin N → ℝ) →L[ℝ] ℝ)
    {i j : Fin N} (hij : i≠j) :
    (twoPhaseUpdateDeriv F' G' i j).det=
      F' (Pi.single i 1)*G' (Pi.single j 1)-F' (Pi.single j 1)*G' (Pi.single i 1) := by
  have hd := continuousLinearMap_det_two_rows (twoPhaseUpdateDeriv F' G' i j) i j hij (by
    intro x l hli hlj
    simp [twoPhaseUpdateDeriv,hli,hlj])
  simpa [ContinuousLinearMap.det,twoPhaseUpdateDeriv,Ne.symm hij] using hd

def coordinateSumLinear (N : ℕ) : (Fin N → ℝ) →L[ℝ] ℝ :=
  ∑ i, ContinuousLinearMap.proj i

theorem coordinateSumLinear_apply {N : ℕ} (x : Fin N → ℝ) :
    coordinateSumLinear N x=∑ i, x i := by simp [coordinateSumLinear]

theorem sumPhaseUpdate_det {N : ℕ} (G' : (Fin N → ℝ) →L[ℝ] ℝ)
    {i j : Fin N} (hij : i≠j) :
    (twoPhaseUpdateDeriv (coordinateSumLinear N) G' i j).det= -G' (pairDirection i j) := by
  rw [twoPhaseUpdateDeriv_det _ _ hij]
  simp [coordinateSumLinear_apply,pairDirection]

theorem pair_curve_deriv_at_recovery {N : ℕ} {G : (Fin N → ℝ) → ℝ}
    {x : Fin N → ℝ} (hG : DifferentiableAt ℝ G x) (i j : Fin N) :
    deriv (fun u => G (pairMidpoint x i j+u • pairDirection i j)) ((x i-x j)/2)=
      fderiv ℝ G x (pairDirection i j) := by
  have hG' : HasFDerivAt G (fderiv ℝ G x)
      (pairMidpoint x i j+((x i-x j)/2) • pairDirection i j) := by
    rw [pairMidpoint_recover]
    exact hG.hasFDerivAt
  exact (hG'.comp_hasDerivAt ((x i-x j)/2)
    (affine_angular_ray_hasDerivAt (pairMidpoint x i j) (pairDirection i j) ((x i-x j)/2))).deriv

end
end IsingBulk.Tail
