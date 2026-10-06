import IsingBulk.Tail.SignedAngularBox
import IsingBulk.Tail.SectorCutoffJetBounds
import IsingBulk.Tail.SectorIntegralDecomposition

/-! The literal nested original/current sectors and their parameter jets
are integrated on the signed fundamental cube with exact periodic weights. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First MeasureTheory Set
open scoped Topology ContDiff

def originalSectorAngularWeight {N : ℕ} (f : SelectorFunctions)
    (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner) (q : Fin N)
    (sigma : Fin N → Fin 3) (theta : Fin N → ℝ) : ℂ :=
  (angularSelector f theta:ℂ)*(nestedSectorWeight b outer inner ho hi q sigma theta:ℝ)

def currentSectorAngularWeight {N : ℕ} (f : SelectorFunctions) (tau : ℝ) (qS : Fin N)
    (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner) (q : Fin N)
    (sigma : Fin N → Fin 3) (theta : Fin N → ℝ) : ℂ :=
  namedCurrentMultiplier f tau qS theta*(nestedSectorWeight b outer inner ho hi q sigma theta:ℝ)

theorem nested_sector_smooth {N : ℕ} (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner)
    (q : Fin N) (sigma : Fin N → Fin 3) : ContDiff ℝ ∞ (nestedSectorWeight b outer inner ho hi q sigma) :=
  (sectorOuterAnchor_smooth b outer ho q).mul (sector_assignment_smooth b inner hi sigma)

theorem originalSectorAngularWeight_regular {N : ℕ} (f : SelectorFunctions) (hf : RegularSelector f)
    (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner) (q : Fin N) (sigma : Fin N → Fin 3) :
    Continuous (originalSectorAngularWeight f b outer inner ho hi q sigma) ∧
      CoordinatePeriodic N (originalSectorAngularWeight f b outer inner ho hi q sigma) := by
  constructor
  · exact (complexSelector_contDiff f hf).continuous.mul
      (Complex.continuous_ofReal.comp (nested_sector_smooth b outer inner ho hi q sigma).continuous)
  · intro theta i
    have he := (nested_sector_weights_periodic f hf b outer inner ho hi q sigma theta i).2.1
    simpa only [originalSectorAngularWeight,Complex.ofReal_mul] using congrArg Complex.ofReal he

theorem currentSectorAngularWeight_regular {N : ℕ} (f : SelectorFunctions) (hf : RegularSelector f)
    (tau : ℝ) (qS : Fin N) (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner)
    (q : Fin N) (sigma : Fin N → Fin 3) :
    Continuous (currentSectorAngularWeight f tau qS b outer inner ho hi q sigma) ∧
      CoordinatePeriodic N (currentSectorAngularWeight f tau qS b outer inner ho hi q sigma) := by
  constructor
  · exact (namedCurrentMultiplier_continuous f hf tau qS).mul
      (Complex.continuous_ofReal.comp (nested_sector_smooth b outer inner ho hi q sigma).continuous)
  · intro theta i
    have he := (nested_sector_weights_periodic f hf b outer inner ho hi q sigma theta i).2.2 qS
    simpa only [currentSectorAngularWeight,namedCurrentMultiplier,Complex.ofReal_mul,mul_assoc] using
      congrArg (fun a : ℝ => -2*Complex.I*(tau:ℂ)*(a:ℂ)) he

theorem original_sector_signed_jets (N : ℕ) (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r tau : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (htau : 0 ≤ tau)
    (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner) (q : Fin N) (sigma : Fin N → Fin 3)
    (s : ℂ) (hs : s∈dampingDomain r) (j : ℕ) :
    iteratedDeriv j (originalSectorIntegral N f r tau b outer inner ho hi (some (q,sigma))) s =
      ∫ theta in signedAngleBox N,originalSectorAngularWeight f b outer inner ho hi q sigma theta *
        iteratedDeriv j (fun z => pulledDensity f r tau 0 z theta) s :=
  weightedAngularIntegral_signed_jets N hN f hf hr hr1 htau le_rfl _
    (originalSectorAngularWeight_regular f hf b outer inner ho hi q sigma).1
    (originalSectorAngularWeight_regular f hf b outer inner ho hi q sigma).2 s hs j

theorem current_sector_signed_jets (N : ℕ) (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r tau lam : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (htau : 0 ≤ tau) (hlam : 0 ≤ lam) (qS : Fin N)
    (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner) (q : Fin N) (sigma : Fin N → Fin 3)
    (s : ℂ) (hs : s∈dampingDomain r) (j : ℕ) :
    iteratedDeriv j (currentSectorIntegral N f r tau lam qS b outer inner ho hi (some (q,sigma))) s =
      ∫ theta in signedAngleBox N,currentSectorAngularWeight f tau qS b outer inner ho hi q sigma theta *
        iteratedDeriv j (fun z => pulledDensity f r tau lam z theta) s :=
  weightedAngularIntegral_signed_jets N hN f hf hr hr1 htau hlam _
    (currentSectorAngularWeight_regular f hf tau qS b outer inner ho hi q sigma).1
    (currentSectorAngularWeight_regular f hf tau qS b outer inner ho hi q sigma).2 s hs j

theorem weighted_nested_jet_support {N : ℕ} (w : (Fin N → ℝ) → ℝ)
    (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner) (q : Fin N)
    (sigma : Fin N → Fin 3) (l : List (Fin N)) :
    tsupport (IsingBulk.Jets.cutoffJet l (fun theta => w theta*nestedSectorWeight b outer inner ho hi q sigma theta)) ⊆
      tsupport (sectorAssignmentWeight b inner hi sigma) :=
  (cutoffJet_tsupport_subset l _).trans (tsupport_mul_subset_right.trans tsupport_mul_subset_right)

end
end IsingBulk.Tail
