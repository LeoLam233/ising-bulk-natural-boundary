import IsingBulk.Anisotropic.NegativeCycles.WindingEllipsoids
import IsingBulk.Anisotropic.NegativeCycles.ConstrainedSpatialCutoff

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.First Set MeasureTheory
open scoped BigOperators

theorem windingAffine_mean_shift (n : ℕ) (k : Fin (n+2)) (d : ℝ)
    (hd : (n+1:ℕ)*d=(2*(k.val:ℝ)-(n+1:ℕ))*Real.pi) (w : Fin n→ℝ) :
    windingAffine n k (fun i => d+w i)=(fun i => d+shapeExtend w i) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [windingAffine,Fin.snoc_last,shapeExtend_last,Finset.sum_add_distrib,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    push_cast at hd ⊢
    linarith
  · simp [windingAffine]

theorem windingAffine_energy_shift (n : ℕ) (k : Fin (n+2)) (d : ℝ)
    (hd : (n+1:ℕ)*d=(2*(k.val:ℝ)-(n+1:ℕ))*Real.pi) (w : Fin n→ℝ) :
    (∑i,(windingAffine n k (fun i => d+w i) i)^2)=
      (n+1:ℕ)*d^2+constrainedSquaredRadius w := by
  rw [windingAffine_mean_shift n k d hd]
  simp only [add_sq,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,←Finset.mul_sum,sum_shapeExtend,mul_zero,add_zero]
  rfl

theorem windingAffine_energy_continuous (n : ℕ) (k : Fin (n+2)) :
    Continuous (fun v : Fin n→ℝ => ∑i,(windingAffine n k v i)^2) := by
  have he : (fun v : Fin n→ℝ => ∑i,(windingAffine n k v i)^2)=
      (fun v => (∑i,(v i)^2)+((2*(k.val:ℝ)-(n+1:ℕ))*Real.pi-∑i,v i)^2) := by
    funext v
    rw [Fin.sum_univ_castSucc]
    simp [windingAffine]
  rw [he]
  fun_prop

/-- Exact Lebesgue translation from each true winding ellipsoid to its zero-mean chart. -/
theorem integral_winding_mean_translation (n : ℕ) (k : Fin (n+2)) (d σ : ℝ)
    (hd : (n+1:ℕ)*d=(2*(k.val:ℝ)-(n+1:ℕ))*Real.pi) (f : (Fin n→ℝ)→ℂ) :
    (∫v in {v | (∑i,(windingAffine n k v i)^2)<σ},f v)=
      ∫w in {w | constrainedSquaredRadius w<σ-(n+1:ℕ)*d^2},f (fun i => d+w i) := by
  let U : Set (Fin n→ℝ) := {v | (∑i,(windingAffine n k v i)^2)<σ}
  let V : Set (Fin n→ℝ) := {w | constrainedSquaredRadius w<σ-(n+1:ℕ)*d^2}
  let c : Fin n→ℝ := fun _ => d
  have hU : MeasurableSet U := measurableSet_lt (windingAffine_energy_continuous n k).measurable measurable_const
  have hV : MeasurableSet V := measurableSet_lt
    ((constrainedSquaredRadius_contDiff (n := n) 0).continuous.measurable) measurable_const
  have hm (w : Fin n→ℝ) : w+c∈U ↔ w∈V := by
    change (∑i,(windingAffine n k (fun i => w i+d) i)^2)<σ ↔ _
    simp_rw [add_comm (w _) d]
    rw [windingAffine_energy_shift n k d hd]
    change (n+1:ℕ)*d^2+constrainedSquaredRadius w<σ ↔ constrainedSquaredRadius w<σ-(n+1:ℕ)*d^2
    constructor <;> intro h <;> linarith
  have he : (fun w => U.indicator f (w+c))=V.indicator (fun w => f (fun i => d+w i)) := by
    funext w
    by_cases hw : w∈V
    · simp only [indicator_of_mem hw,indicator_of_mem ((hm w).mpr hw)]
      congr 1
      funext i
      exact add_comm _ _
    · simp only [indicator_of_notMem hw,indicator_of_notMem (not_congr (hm w) |>.mpr hw)]
  have ht := integral_add_right_eq_self (μ := volume) (U.indicator f) c
  rw [he,integral_indicator hV,integral_indicator hU] at ht
  exact ht.symm

end IsingBulk.Anisotropic.NegativeCycles
