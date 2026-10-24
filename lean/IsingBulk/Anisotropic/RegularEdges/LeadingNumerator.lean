import IsingBulk.Anisotropic.RegularEdges.ComplexAngular
import IsingBulk.Anisotropic.RegularEdges.PhaseProducts
import IsingBulk.First.ActualVandermonde

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail Set Filter
open scoped Topology BigOperators

def edgeAngularWeight {N : ℕ} (b : ℝ) (B S : ℂ→ℂ) (u : ℂ) (q : Fin N→ℝ) : ℂ :=
  (B u)^(N.choose 2)*(S u)⁻¹^N *
    (∏ i,2*edgeParamRoot b B u (q i)/(1-edgeParamRoot b B u (q i)^2)) *
    (∏ p∈firstStrictPairs N, angularRootPair (edgeParamRoot b B u (q p.1))
      (edgeParamRoot b B u (q p.2)) (q p.1:ℂ) (q p.2:ℂ))

def edgeAngularDensity {N : ℕ} (b : ℝ) (B S : ℂ→ℂ) (u : ℂ) (q : Fin N→ℝ) : ℂ :=
  edgeAngularWeight b B S u q*((1+edgeRootProduct b B u q)/(1-edgeRootProduct b B u q))

/-- Coincidence-safe regular factor: no coordinate difference appears in a denominator. -/
def edgeRegularAmplitude {N : ℕ} (b : ℝ) (B S : ℂ→ℂ) (u : ℂ) (q : Fin N→ℝ) : ℂ :=
  (B u)^(N.choose 2)*(S u)⁻¹^N *
    (∏ i,2*edgeParamRoot b B u (q i)/(1-edgeParamRoot b B u (q i)^2)) *
    (∏ p∈firstStrictPairs N, (Real.sinc ((q p.1-q p.2)/2):ℂ)^2 *
      (edgeParamRoot b B u (q p.1)*edgeParamRoot b B u (q p.2)/
        (1-edgeParamRoot b B u (q p.1)*edgeParamRoot b B u (q p.2))^2))

theorem angularRootPair_vandermonde (a b : ℂ) (q t : ℝ) :
    angularRootPair a b (q:ℂ) (t:ℂ)=((q-t:ℝ):ℂ)^2 *
      (Real.sinc ((q-t)/2):ℂ)^2*(a*b/(1-a*b)^2) := by
  have hs : ((q-t:ℝ):ℂ)*(Real.sinc ((q-t)/2):ℂ)=2*(Real.sin ((q-t)/2):ℂ) := by
    exact_mod_cast (show (q-t)*Real.sinc ((q-t)/2)=2*Real.sin ((q-t)/2) by
      have h := real_mul_sinc ((q-t)/2)
      linarith)
  have hs2 := congrArg (fun x : ℂ => x^2) hs
  unfold angularRootPair
  rw [show ((q:ℂ)-(t:ℂ))/2=(((q-t)/2:ℝ):ℂ) by push_cast; ring,←Complex.ofReal_sin]
  linear_combination -a*b/(1-a*b)^2*hs2

/-- Exact Vandermonde cancellation for the complete local angular numerator, including coincidences. -/
theorem edgeAngularWeight_factorization {N : ℕ} (b : ℝ) (B S : ℂ→ℂ) (u : ℂ) (q : Fin N→ℝ) :
    edgeAngularWeight b B S u q=(firstVandermonde q:ℂ)^2*edgeRegularAmplitude b B S u q := by
  have hp : (∏ p∈firstStrictPairs N, angularRootPair (edgeParamRoot b B u (q p.1))
      (edgeParamRoot b B u (q p.2)) (q p.1:ℂ) (q p.2:ℂ))=
      (firstVandermonde q:ℂ)^2*(∏ p∈firstStrictPairs N, (Real.sinc ((q p.1-q p.2)/2):ℂ)^2 *
      (edgeParamRoot b B u (q p.1)*edgeParamRoot b B u (q p.2)/
        (1-edgeParamRoot b B u (q p.1)*edgeParamRoot b B u (q p.2))^2)) := by
    simp_rw [angularRootPair_vandermonde,mul_assoc]
    rw [Finset.prod_mul_distrib]
    congr 1
    simp [firstVandermonde,Finset.prod_pow]
  unfold edgeAngularWeight edgeRegularAmplitude
  rw [hp]
  ring

theorem edgeAngularDensity_factorization {N : ℕ} (b : ℝ) (B S : ℂ→ℂ) (u : ℂ) (q : Fin N→ℝ) :
    edgeAngularDensity b B S u q=(firstVandermonde q:ℂ)^2*
      (edgeRegularAmplitude b B S u q*(1+edgeRootProduct b B u q))/(1-edgeRootProduct b B u q) := by
  rw [edgeAngularDensity,edgeAngularWeight_factorization]
  ring

theorem edgeRegularAmplitude_collision (N : ℕ) (b : ℝ) (B S : ℂ→ℂ) :
    edgeRegularAmplitude b B S 0 (0:Fin N→ℝ)=
      (B 0)^(N.choose 2)*(S 0)⁻¹^N *
      (2*continuedRoot (b:ℂ)/(1-continuedRoot (b:ℂ)^2))^N *
      (continuedRoot (b:ℂ)^2/(1-continuedRoot (b:ℂ)^2)^2)^(N.choose 2) := by
  simp [edgeRegularAmplitude,edgeParamRoot,edgeParamW,firstStrictPairs_card,pow_two,div_pow]

theorem edgeRegularAmplitude_collision_ne_zero {N : ℕ} {b : ℝ} {B S : ℂ→ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hS : S 0≠0) :
    edgeRegularAmplitude b B S 0 (0:Fin N→ℝ)≠0 := by
  have hB0 : B 0≠0 := by intro h; simp [h] at hB
  have hr := continuedRoot_nonzero (b:ℂ)
  have hd : 1-continuedRoot (b:ℂ)^2≠0 := by
    have hh := edgeRoot_pair_denominator_ne_zero hb hB 0 0
    simpa [edgeRoot,edgeW,pow_two] using hh
  rw [edgeRegularAmplitude_collision]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hB0) (pow_ne_zero _ (inv_ne_zero hS)))
    (pow_ne_zero _ (div_ne_zero (mul_ne_zero (by norm_num) hr) hd)))
    (pow_ne_zero _ (div_ne_zero (pow_ne_zero _ hr) (pow_ne_zero _ hd)))

end
end IsingBulk.Anisotropic.RegularEdges
