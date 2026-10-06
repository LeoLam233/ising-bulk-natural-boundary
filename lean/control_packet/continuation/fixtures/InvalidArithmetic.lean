/- INTENTIONALLY INVALID. Excluded from production imports and declaration counts. -/
example : (0 : Nat) = 1 := by
  -- EXPECT_FAILURE_HERE: false equality, not an import or startup failure.
  rfl
