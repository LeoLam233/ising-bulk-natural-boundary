import IsingBulk.Anisotropic.NegativeNormalForm.CentralGaussianEnvelopes
import IsingBulk.Anisotropic.NegativeDominance.GaussianErrorSum
import IsingBulk.Anisotropic.NegativeDominance.GaussianEnvelopeAlgebra

noncomputable section
namespace IsingBulk.Joint.Negative
open IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm IsingBulk.Anisotropic.NegativeDominance
open MeasureTheory
open scoped BigOperators

/-- The exact dependent-if SAME-R0 remainder sum from the physical decomposition,
for any selected winding subset. The actual individual compact-jet estimates
imply a sharp Gaussian with coefficient one on j log N. Inactive sectors are
zero; no chosen poles or remainders are replaced. -/
theorem uniform_winding_remainder_sum_gaussian (K M c sigma : ℝ)
    (hK : 0<K) (hM : 1≤M) (hc : 0<c) (hsigma : 0<sigma) :
    ∃g D : ℝ,0<g ∧ 0<D ∧ ∀(B rootB R₀ : ℂ→ℂ) (phi : ℝ) (hphi : Real.sin phi≠0), ∀m j : ℕ,∀d : Fin (2*m+2)→ℝ,∀s : ℝ,s≤sigma →
      ∀T : (k : Fin (2*m+2))→(2*m+1:ℕ)*(d k)^2<s → Config (2*m+1)→ℂ,
      ∀S : Finset (Fin (2*m+2)),
      (∀k∈S,∀hk : (2*m+1:ℕ)*(d k)^2<s,
        ‖iteratedDeriv j (centeredInnerRemainder B rootB phi hphi R₀ m (d k) s (T k hk)) 0/(j.factorial:ℂ)‖≤
          ((volume (centeredInnerSet (2*m) (d k) s)).toReal*(K*remainderGaussianEnvelope M m))/
            ((c/(2*m+1:ℕ))/2)^j) →
      ‖∑k∈S,if hk : (2*m+1:ℕ)*(d k)^2<s then
          iteratedDeriv j (centeredInnerRemainder B rootB phi hphi R₀ m (d k) s (T k hk)) 0/(j.factorial:ℂ)
        else 0‖≤gaussianEnvelope g D (2*m+1) j := by
  obtain ⟨g,D,hg,hD,hbound⟩ := centeredRemainderEnvelope_gaussian_bound K M c sigma hK hM hc hsigma
  refine ⟨g/2,D+1/(2*g),by positivity,by positivity,?_⟩
  intro B rootB R₀ phi hphi m j d s hs T S hjet
  let E := Real.exp (-g*(2*m+1:ℕ)^2+((j:ℝ)+1)*Real.log (2*m+1:ℕ)+D*((j:ℝ)+1))
  have hE : 0≤E := (Real.exp_pos _).le
  have hterm (k : Fin (2*m+2)) (hkS : k∈S) :
      ‖if hk : (2*m+1:ℕ)*(d k)^2<s then
          iteratedDeriv j (centeredInnerRemainder B rootB phi hphi R₀ m (d k) s (T k hk)) 0/(j.factorial:ℂ)
        else 0‖≤E := by
    split_ifs with hk
    · exact (hjet k hkS hk).trans (hbound m j (d k) s hs)
    · simpa only [norm_zero] using hE
  have hcard : (S.card:ℝ)≤((2*m+1:ℕ):ℝ)+1 := by
    have hh : S.card≤(2*m+1)+1 := by
      simpa only [Fintype.card_fin,Nat.add_assoc] using S.card_le_univ
    exact_mod_cast hh
  calc
    _ ≤ ∑k∈S,‖if hk : (2*m+1:ℕ)*(d k)^2<s then
          iteratedDeriv j (centeredInnerRemainder B rootB phi hphi R₀ m (d k) s (T k hk)) 0/(j.factorial:ℂ)
        else 0‖ := norm_sum_le _ _
    _ ≤ ∑_k∈S,E := Finset.sum_le_sum hterm
    _ = (S.card:ℝ)*E := by simp
    _ ≤ (((2*m+1:ℕ):ℝ)+1)*E := mul_le_mul_of_nonneg_right hcard hE
    _ ≤ gaussianEnvelope (g/2) (D+1/(2*g)) (2*m+1) j :=
      gaussian_winding_count hg D (2*m+1) j

end IsingBulk.Joint.Negative
