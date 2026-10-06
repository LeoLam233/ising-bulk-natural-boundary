import IsingBulk.First.RealFredholmIdentification
import IsingBulk.First.PublishedFixedOrder

/-! Narrow separated E1/E2 boundaries. Both apply only to real low-temperature
physical data. All complex continuation, noncancellation and tail bounds stay
internal. E3 is the existing fixed-order non-Nickel full-site input. -/
namespace IsingBulk.Final
noncomputable section
open IsingBulk.First
open scoped BigOperators

/-- E1: Palmer--Tracy 1981 Theorem 5.0/proof pp.374--378, in the published
Tracy--Widom 2014 Appendix 1 (7)--(8), with the manuscript section 2/Appendix F
normalized offsite convention. M is the real physical squared magnetization;
no formula or complex analyticity for it is included here. -/
def RealFredholmE1 (X : ℂ → ℂ) (M : ℝ → ℂ) : Prop :=
  ∀ x : ℝ, 1 < x → ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ < 1 ∧
    ∀ r : ℝ, r₀ < r → r < 1 →
      Summable (fun n : ℕ => doubleFormFactor (2*(n+1)) r (x:ℂ)) ∧
      X (x:ℂ) = 1-M x+2*M x*(∑' n : ℕ, doubleFormFactor (2*(n+1)) r (x:ℂ))

/-- E2: Yang 1952 spontaneous squared magnetization, real low temperature.
The chosen fourth root tends to one at infinity, as proved for the expression.
Local complex branch regularity/nonvanishing is established internally. -/
def YangMagnetizationE2 (M : ℝ → ℂ) : Prop :=
  ∀ x : ℝ, 1 < x → M x = magnetizationSquared (x:ℂ)

theorem normalized_real_representation_of_E1_E2 {X : ℂ → ℂ} {M : ℝ → ℂ}
    (hE1 : RealFredholmE1 X M) (hE2 : YangMagnetizationE2 M) :
    RealNormalizedFredholmRepresentation X := by
  intro x hx
  obtain ⟨r₀,hr₀,hr₀1,hrep⟩ := hE1 x hx
  refine ⟨r₀,hr₀,hr₀1,?_⟩
  intro r hr hr1
  obtain ⟨hs,hX⟩ := hrep r hr hr1
  refine ⟨hs,?_⟩
  simpa only [hE2 x hx,normalizedBulkSeries] using hX

end
end IsingBulk.Final
