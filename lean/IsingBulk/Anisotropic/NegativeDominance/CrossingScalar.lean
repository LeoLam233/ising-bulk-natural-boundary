import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section

/-- Elementary assembly of rigorously bounded contributions to a logarithmic
model ratio. This lemma contains no asymptotic or dominance premise. -/
theorem crossing_components_bounds (X b q L u C E T G P R : ℝ)
    (hX : 1 ≤ X) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hb : X ≤ b ∧ b ≤ 2*X) (hE : -10*X ≤ E ∧ E ≤ 0)
    (hT : X*u/2 ≤ T ∧ T ≤ 3*X*u)
    (hG : 0 ≤ G ∧ G ≤ b) (hP : -2*X ≤ P ∧ P ≤ 0)
    (hR : -2*C ≤ R ∧ R ≤ 2*C) :
    let K := 2*|q|+14+2*C;
    X*(-2*L+u/2-K) ≤ E+b*(q-L)+T+G+P+R ∧
      E+b*(q-L)+T+G+P+R ≤ X*(-L+3*u+K) := by
  dsimp
  have hX0 : 0 ≤ X := by linarith
  have hb0 : 0 ≤ b := hX0.trans hb.1
  have hq : |b*q| ≤ 2*X*|q| := by
    rw [abs_mul, abs_of_nonneg hb0]
    exact mul_le_mul_of_nonneg_right hb.2 (abs_nonneg q)
  have hq' := abs_le.mp hq
  have hbl := mul_le_mul_of_nonneg_right hb.1 hL
  have hbu := mul_le_mul_of_nonneg_right hb.2 hL
  have hCX := mul_le_mul_of_nonneg_left hX (show 0 ≤ 2*C by positivity)
  constructor <;> nlinarith [hE.1, hE.2, hT.1, hT.2, hG.1, hG.2, hP.1, hP.2,
    hR.1, hR.2, hq'.1, hq'.2, abs_nonneg q]

end
end IsingBulk.Anisotropic.NegativeDominance
