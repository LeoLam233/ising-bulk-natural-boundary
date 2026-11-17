import IsingBulk.AnisoF002.RegularTail.VandermondeBlock
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
# The actual independent-coordinate measure on the constrained real plane

Here `d` is the number of independent coordinates and `d + 1` is the
particle number.  The norm is the ambient Euclidean norm, so its square
is exactly `Q = sum_i v_i^2`.  The measure is the pushforward of ordinary
Lebesgue measure in the first `d` coordinates; no surface-measure
normalization is substituted for the measure in frozen F002, Lemma 4.2.
-/

namespace IsingBulk.AnisoF002.NegativeHT.Angular
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

abbrev Ambient (d : ℕ) := EuclideanSpace ℝ (Fin (d + 1))

def constrainedPlane (d : ℕ) : Submodule ℝ (Ambient d) where
  carrier := {v | ∑ i, v i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw
    change ∑ i, (v i + w i) = 0
    rw [Finset.sum_add_distrib, hv, hw, add_zero]
  smul_mem' := by
    intro a v hv
    change ∑ i, a * v i = 0
    rw [← Finset.mul_sum, hv, mul_zero]

theorem constrained_sum {d : ℕ} (v : constrainedPlane d) :
    ∑ i, (v : Ambient d) i = 0 := v.property

/-- Exactly the chart `v_(d+1) = -sum_(i≤d) v_i` used in the frozen proof. -/
def independentChart (d : ℕ) : (Fin d → ℝ) ≃ₗ[ℝ] constrainedPlane d where
  toFun x := ⟨WithLp.toLp 2 (Fin.snoc x (-∑ i, x i)), by
    change ∑ i, Fin.snoc x (-∑ j, x j) i = 0
    simp [Fin.sum_univ_castSucc]⟩
  invFun v := fun i => (v : Ambient d) i.castSucc
  left_inv x := by funext i; simp
  right_inv v := by
    apply Subtype.ext
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have hv := constrained_sum v
      rw [Fin.sum_univ_castSucc] at hv
      simp only [Fin.snoc_last]
      change -(∑ j : Fin d, (v : Ambient d) j.castSucc) = (v : Ambient d) (Fin.last d)
      linarith
    · simp
  map_add' x y := by
    apply Subtype.ext
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [Finset.sum_add_distrib, add_comm]
    · simp
  map_smul' a x := by
    apply Subtype.ext
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [← Finset.mul_sum]
    · simp

@[simp] theorem independentChart_castSucc (d : ℕ) (x : Fin d → ℝ) (i : Fin d) :
    (independentChart d x : Ambient d) i.castSucc = x i := by
  simp [independentChart]

@[simp] theorem independentChart_last (d : ℕ) (x : Fin d → ℝ) :
    (independentChart d x : Ambient d) (Fin.last d) = -∑ i, x i := by
  simp [independentChart]

theorem constrained_finrank (d : ℕ) : Module.finrank ℝ (constrainedPlane d) = d := by
  rw [← (independentChart d).finrank_eq]
  simp

/-- The literal `dv_1 ... dv_d` measure, transported to the constrained plane. -/
def independentMeasure (d : ℕ) : Measure (constrainedPlane d) :=
  volume.map (independentChart d)

instance independentMeasure_isAddHaar (d : ℕ) :
    (independentMeasure d).IsAddHaarMeasure := by
  unfold independentMeasure
  infer_instance

theorem independentChart_measurePreserving (d : ℕ) :
    MeasurePreserving (independentChart d) volume (independentMeasure d) := by
  exact ⟨(independentChart d).toContinuousLinearEquiv.continuous.measurable, rfl⟩

theorem constrained_norm_sq {d : ℕ} (v : constrainedPlane d) :
    ‖v‖ ^ 2 = ∑ i, (v : Ambient d) i ^ 2 :=
  EuclideanSpace.real_norm_sq_eq (v : Ambient d)

def planeVandermonde {d : ℕ} (v : constrainedPlane d) : ℝ :=
  RegularTail.vandermondeSquared (fun i => (v : Ambient d) i)

theorem planeVandermonde_nonneg {d : ℕ} (v : constrainedPlane d) :
    0 ≤ planeVandermonde v := RegularTail.vandermondeSquared_nonneg _

theorem continuous_planeVandermonde (d : ℕ) :
    Continuous (planeVandermonde : constrainedPlane d → ℝ) := by
  unfold planeVandermonde RegularTail.vandermondeSquared
  fun_prop

theorem planeVandermonde_scaling {d : ℕ} (v : constrainedPlane d) (r : ℝ) :
    planeVandermonde (r • v) = r ^ (2 * (d + 1).choose 2) * planeVandermonde v := by
  exact RegularTail.vandermonde_scaling _ r

theorem planeVandermonde_pos_of_injective {d : ℕ} (v : constrainedPlane d)
    (hv : Function.Injective (fun i => (v : Ambient d) i)) :
    0 < planeVandermonde v := by
  apply Finset.prod_pos
  intro ij hij
  have hij' : ij.1 < ij.2 := (Finset.mem_filter.mp hij).2
  exact sq_pos_of_ne_zero (sub_ne_zero.mpr (fun h => (ne_of_lt hij') (hv h)))

theorem independentChart_positive_coordinates_injective {d : ℕ} (hd : 0 < d) :
    Function.Injective (fun i =>
      (independentChart d (fun j : Fin d => (j.val : ℝ) + 1) : Ambient d) i) := by
  let x : Fin d → ℝ := fun j => (j.val : ℝ) + 1
  have hx (i : Fin d) : 0 < x i := by dsimp [x]; positivity
  have hsum : 0 < ∑ i, x i := by
    apply Finset.sum_pos (fun i _ => hx i)
    exact ⟨⟨0, hd⟩, Finset.mem_univ _⟩
  change Function.Injective (fun i => (independentChart d x : Ambient d) i)
  intro i j hij
  revert hij
  refine Fin.lastCases ?_ (fun i' => ?_) i
  · refine Fin.lastCases ?_ (fun j' => ?_) j
    · intro _; rfl
    · simp only [independentChart_last, independentChart_castSucc]
      intro h
      linarith [hx j']
  · refine Fin.lastCases ?_ (fun j' => ?_) j
    · simp only [independentChart_last, independentChart_castSucc]
      intro h
      linarith [hx i']
    · simp only [independentChart_castSucc]
      intro h
      apply congrArg Fin.castSucc
      apply Fin.ext
      have he : (i'.val : ℝ) = (j'.val : ℝ) := by simpa [x] using h
      exact_mod_cast he

theorem exists_planeVandermonde_pos {d : ℕ} (hd : 0 < d) :
    ∃ v : constrainedPlane d, v ≠ 0 ∧ 0 < planeVandermonde v := by
  let v := independentChart d (fun j : Fin d => (j.val : ℝ) + 1)
  have hv : v ≠ 0 := by
    intro h
    have hh := congrArg (fun w : constrainedPlane d => (independentChart d).symm w ⟨0, hd⟩) h
    simp [v] at hh
  exact ⟨v, hv, planeVandermonde_pos_of_injective v
    (independentChart_positive_coordinates_injective hd)⟩

end
end IsingBulk.AnisoF002.NegativeHT.Angular
