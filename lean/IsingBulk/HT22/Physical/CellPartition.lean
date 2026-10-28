import IsingBulk.HT22.Physical.PopulationPartition

namespace IsingBulk.HT22.Physical
noncomputable section
open Set MeasureTheory IsingBulk.Preferred22
open scoped BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

def rightPopulationIntegral (negative : Bool) (n : ℕ) (τ : ℝ)
    (η p m r : ℝ → ℝ) (t : ℂ) : ℂ :=
  weightedContourIntegral negative n τ p m (preferredCellWeight .right η p m r) t

def anchorPopulationIntegral (negative : Bool) (n : ℕ) (a : Fin (n+1)) (τ : ℝ)
    (η p m r : ℝ → ℝ) (t : ℂ) : ℂ :=
  weightedContourIntegral negative n τ p m (preferredCellWeight (.anchor a) η p m r) t

theorem weightedContourIntegral_integrable (negative : Bool) (n : ℕ)
    (τ : ℝ) (p m : ℝ → ℝ) (t : ℂ)
    (hbare : Continuous (bareContourDensity negative τ p m t (N := n+1)))
    (w : (Fin (n+1) → ℝ) → ℝ) (hw : Continuous w) :
    IntegrableOn (fun q => (w (constrainedAngles negative n q):ℂ)*
      bareContourDensity negative τ p m t (constrainedAngles negative n q)) (angularBox n) := by
  exact continuous_integrableOn_angularBox
    ((Complex.continuous_ofReal.comp (hw.comp (constrainedAngles_continuous negative n))).mul
      (hbare.comp (constrainedAngles_continuous negative n)))

theorem lower_population_eq_right_add_anchors (negative : Bool) (n : ℕ)
    (τ : ℝ) (η p m r : ℝ → ℝ) (t : ℂ)
    (hbare : Continuous (bareContourDensity negative τ p m t (N := n+1)))
    (hη : Continuous η) (hp : Continuous p) (hm : Continuous m) (hr : Continuous r) :
    lowerPopulationIntegral negative n τ η p m t =
      rightPopulationIntegral negative n τ η p m r t +
        ∑ a : Fin (n+1), anchorPopulationIntegral negative n a τ η p m r t := by
  have hw (cell : PreferredTransportCell (n+1)) :
      Continuous (preferredCellWeight cell η p m r) := by
    unfold preferredCellWeight preferredLowerWeight lowerWeight occupancy
    cases cell
    · unfold preferredRightWeight
      fun_prop
    · unfold preferredAnchorWeight
      fun_prop
  have hi (cell) := weightedContourIntegral_integrable negative n τ p m t hbare
    (preferredCellWeight cell η p m r) (hw cell)
  unfold lowerPopulationIntegral rightPopulationIntegral anchorPopulationIntegral weightedContourIntegral
  rw [← integral_finsetSum _ (fun a _ => hi (.anchor a)),← integral_add (hi .right)
    (integrable_finsetSum _ (fun a _ => hi (.anchor a)))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun θ => by
    dsimp only
    simp_rw [preferredCellWeight]
    rw [← Finset.sum_mul,← add_mul,← Complex.ofReal_sum,← Complex.ofReal_add]
    congr 2
    rw [← Finset.mul_sum,← mul_add,preferred_anchor_telescope,mul_one]

end
end IsingBulk.HT22.Physical
