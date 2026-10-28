import IsingBulk.Preferred22.Pfaffian

/-!
# F001: the dispersion ghost relation, without a limiting branch

The four-point cleared identity and all-even Pfaffian propagation are reused
from `Preferred22.Pfaffian`, whose proofs are purely algebraic. The new
three-point identity below is the four-point identity with the ghost at
infinity, proved directly on the dispersion curve. In particular no formal
asymptotic expansion or analytic-continuation premise is required.
-/

namespace IsingBulk.HT22.Algebra

open IsingBulk.Preferred22

section Field
variable {𝕜 : Type*} [Field 𝕜]

/-- The cleared cross denominator of the three physical points. -/
theorem three_point_cross (a b c u v w : 𝕜)
    (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) :
    (a-b)*(1-u*w)*(1-v*w) - (a-c)*(1-u*v)*(1-v*w) +
      (b-c)*(1-u*v)*(1-u*w) =
    (u*v*w)*(a*((w+w⁻¹)-(v+v⁻¹)) +
      b*((u+u⁻¹)-(w+w⁻¹)) + c*((v+v⁻¹)-(u+u⁻¹))) := by
  field_simp
  ring

/-- The three-column Vandermonde calculation after using the dispersion curve. -/
theorem three_point_vandermonde (S a b c : 𝕜)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    a*((2*S-c-c⁻¹)-(2*S-b-b⁻¹)) +
      b*((2*S-a-a⁻¹)-(2*S-c-c⁻¹)) +
      c*((2*S-b-b⁻¹)-(2*S-a-a⁻¹)) =
      -(a-b)*(a-c)*(b-c)/(a*b*c) := by
  field_simp
  ring

/-- Cleared ghost identity, valid also when one of the pair gaps vanishes. -/
theorem three_point_dispersion_cleared (S a b c u v w : 𝕜)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (h1 : a+a⁻¹+u+u⁻¹ = 2*S)
    (h2 : b+b⁻¹+v+v⁻¹ = 2*S)
    (h3 : c+c⁻¹+w+w⁻¹ = 2*S) :
    (a-b)*(1-u*w)*(1-v*w) - (a-c)*(1-u*v)*(1-v*w) +
      (b-c)*(1-u*v)*(1-u*w) =
      -(u*v*w)*((a-b)*(a-c)*(b-c))/(a*b*c) := by
  have h1' : u+u⁻¹ = 2*S-a-a⁻¹ := by linear_combination h1
  have h2' : v+v⁻¹ = 2*S-b-b⁻¹ := by linear_combination h2
  have h3' : w+w⁻¹ = 2*S-c-c⁻¹ := by linear_combination h3
  rw [three_point_cross a b c u v w hu hv hw, h1', h2', h3',
    three_point_vandermonde S a b c ha hb hc]
  ring

/-- The exact scalar ghost identity on the pole-free dispersion locus. -/
theorem three_point_dispersion (S a b c u v w : 𝕜)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (h1 : a+a⁻¹+u+u⁻¹ = 2*S)
    (h2 : b+b⁻¹+v+v⁻¹ = 2*S)
    (h3 : c+c⁻¹+w+w⁻¹ = 2*S)
    (h12 : 1-u*v ≠ 0) (h13 : 1-u*w ≠ 0) (h23 : 1-v*w ≠ 0) :
    dispersionB a b u v - dispersionB a c u w + dispersionB b c v w =
      -((u/a)*(v/b)*(w/c)) *
        (dispersionB a b u v * dispersionB a c u w * dispersionB b c v w) := by
  have h := three_point_dispersion_cleared S a b c u v w
    ha hb hc hu hv hw h1 h2 h3
  unfold dispersionB
  field_simp
  field_simp at h
  linear_combination h

end Field

/-- Scaling the ghost relation into the genuine four-point Pfaffian equation. -/
theorem scaled_three_point (r1 r2 r3 b12 b13 b23 : ℂ)
    (hB : b12-b13+b23 = -(r1^2*r2^2*r3^2)*(b12*b13*b23)) :
    r1*scaledPair r2 r3 b23 - r2*scaledPair r1 r3 b13 +
      r3*scaledPair r1 r2 b12 =
      r1*r2*r3*scaledPair r1 r2 b12*scaledPair r1 r3 b13*
        scaledPair r2 r3 b23 := by
  unfold scaledPair
  linear_combination
    (-Complex.I*r1*r2*r3)*hB +
    (Complex.I*(r1*r2*r3)^3*b12*b13*b23)*Complex.I_sq

end IsingBulk.HT22.Algebra
