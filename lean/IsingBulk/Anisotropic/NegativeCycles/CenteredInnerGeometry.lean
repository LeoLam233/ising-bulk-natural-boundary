import IsingBulk.Anisotropic.NegativeCycles.CutoffLocalization
import IsingBulk.Anisotropic.NegativeCycles.ShiftedInnerPole

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm Set MeasureTheory
open scoped BigOperators

def centeredInnerSet (n : ℕ) (d σ : ℝ) : Set (Fin n→ℝ) :=
  {q | constrainedSquaredRadius q<σ-(n+1:ℕ)*d^2}

def centeredInnerCompact (n : ℕ) (d σ : ℝ) : Set (Fin n→ℝ) :=
  {q | constrainedSquaredRadius q≤σ-(n+1:ℕ)*d^2}

def centeredInnerAngles (n : ℕ) (d : ℝ) (q : Fin n→ℝ) : Config (n+1) :=
  fun i => ((d+shapeExtend q i:ℝ):ℂ)

theorem centeredInnerSet_measurable (n : ℕ) (d σ : ℝ) : MeasurableSet (centeredInnerSet n d σ) :=
  (isOpen_lt (constrainedSquaredRadius_contDiff 0).continuous continuous_const).measurableSet

theorem centeredInnerSet_subset_compact (n : ℕ) (d σ : ℝ) :
    centeredInnerSet n d σ⊆centeredInnerCompact n d σ := by
  intro q hq
  exact (show constrainedSquaredRadius q<σ-(n+1:ℕ)*d^2 from hq).le

theorem centeredInnerCompact_isCompact (n : ℕ) (d σ : ℝ) : IsCompact (centeredInnerCompact n d σ) := by
  let a := σ-(n+1:ℕ)*d^2
  apply IsCompact.of_isClosed_subset
    (isCompact_constrained_squared_sublevel (n := n) (Real.sqrt (max a 0)) (Real.sqrt_nonneg _))
    (isClosed_le (constrainedSquaredRadius_contDiff 0).continuous continuous_const)
  intro q hq
  rw [Real.sq_sqrt (le_max_right a 0)]
  exact hq.trans (le_max_left a 0)

theorem centeredInnerAngles_continuous (n : ℕ) (d : ℝ) : Continuous (centeredInnerAngles n d) := by
  unfold centeredInnerAngles
  have hshape : Continuous (fun q : Fin n→ℝ => shapeExtend q) :=
    continuous_pi continuous_shapeExtend_eval
  exact continuous_pi (fun i => Complex.continuous_ofReal.comp
    (continuous_const.add ((continuous_apply i).comp hshape)))

theorem centeredInnerAngles_energy (n : ℕ) (d : ℝ) (q : Fin n→ℝ) :
    absoluteEnergy (centeredInnerAngles n d q)=(n+1:ℕ)*d^2+constrainedSquaredRadius q := by
  simp only [absoluteEnergy,centeredInnerAngles,Complex.norm_real,Real.norm_eq_abs,sq_abs,add_sq]
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hz := sum_shapeExtend q
  rw [←Finset.mul_sum,hz,mul_zero,add_zero]
  rfl

@[simp] theorem shiftedInnerPole_centered_angles {n : ℕ} (d : ℝ) (T : Config (n+1)→ℂ)
    (q : Fin n→ℝ) : shiftedInnerPole (d:ℂ) T (centeredInnerAngles n d q)=
      T (shapeExtend (complexify n q)) := by
  unfold shiftedInnerPole centeredInnerAngles
  congr 1
  funext i
  rw [Complex.ofReal_add,add_sub_cancel_left]
  exact (congrFun (shapeExtend_complexify n q) i).symm

end IsingBulk.Anisotropic.NegativeCycles
