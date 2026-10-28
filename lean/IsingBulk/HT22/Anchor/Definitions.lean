import IsingBulk.HT22.Tail.PairFactorization
import IsingBulk.Preferred22.AnchorAmplitude

namespace IsingBulk.HT22.Anchor
noncomputable section
open IsingBulk.Preferred22
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false

def inverseGauge (t q : ℂ) : ℂ := Complex.exp (Complex.I*(q+preferredMovingBranch t)/2)

def ordinaryPair (t q r : ℂ) : ℂ := Algebra.ordinaryEntry
  (Complex.exp (Complex.I*preferredMovingInverse t q))
  (Complex.exp (Complex.I*preferredMovingInverse t r))
  (preferredRegularDiskRoot t q) (preferredRegularDiskRoot t r)

theorem ordinaryPair_eq_gauged (t q r : ℂ) :
    ordinaryPair t q r = inverseGauge t q*inverseGauge t r*preferredRegularPair t q r := by
  let w : Fin 2 → ℂ := ![preferredMovingInverse t q,preferredMovingInverse t r]
  let φ : Fin 2 → ℂ := ![preferredRegularPhase t q,preferredRegularPhase t r]
  have h := canonicalPhaseGauge_halfAngle w φ 0 1
  have hq : inverseGauge t q*canonicalPhaseGauge w φ 0=1 := by
    unfold inverseGauge canonicalPhaseGauge
    simp only [w,φ,Matrix.cons_val_zero,preferredRegularPhase,← Complex.exp_add]
    convert Complex.exp_zero using 1
    ring
  have hr : inverseGauge t r*canonicalPhaseGauge w φ 1=1 := by
    unfold inverseGauge canonicalPhaseGauge
    simp only [w,φ,Matrix.cons_val_one,Matrix.cons_val_zero,preferredRegularPhase,← Complex.exp_add]
    convert Complex.exp_zero using 1
    ring
  have hh := congrArg (fun x => inverseGauge t q*inverseGauge t r*x) h
  have he : inverseGauge t q*inverseGauge t r*
      (-Complex.I*canonicalPhaseGauge w φ 0*canonicalPhaseGauge w φ 1*
       (Complex.exp (Complex.I*w 0)-Complex.exp (Complex.I*w 1))/
       (1-Complex.exp (-Complex.I*φ 0)*Complex.exp (-Complex.I*φ 1))) =
      ordinaryPair t q r := by
    unfold ordinaryPair Algebra.ordinaryEntry dispersionB preferredRegularDiskRoot
    calc
      _ = (inverseGauge t q*canonicalPhaseGauge w φ 0)*
          (inverseGauge t r*canonicalPhaseGauge w φ 1)*
          (-Complex.I*(Complex.exp (Complex.I*w 0)-Complex.exp (Complex.I*w 1))/
          (1-Complex.exp (-Complex.I*φ 0)*Complex.exp (-Complex.I*φ 1))) := by ring
      _ = _ := by
        rw [hq,hr]
        simp only [w,φ,Matrix.cons_val_zero,Matrix.cons_val_one,one_mul]
        ring
  rw [he] at hh
  exact hh

def borderedKernel {N : ℕ} (t : ℂ) (q : Fin N → ℂ) : Matrix (Fin (N+1)) (Fin (N+1)) ℂ :=
  Algebra.ghostBorder (fun i j => ordinaryPair t (q i) (q j)) (fun _ => 1)

def amplitude {N : ℕ} (σ t : ℂ) (q : Fin N → ℂ) : ℂ :=
  let Z := ∏ i,preferredRegularDiskRoot t (q i)
  ((1+σ*Z)/(1-σ*Z))*(borderedKernel t q).det*(∏ i,preferredRegularOneBody t (q i)) /
    ((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))

end
end IsingBulk.HT22.Anchor
