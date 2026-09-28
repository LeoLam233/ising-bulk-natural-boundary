# Reporting mathematical issues

Please identify the manuscript version/hash and the exact numbered statement. Explain the support, branches, parameter range and constant dependencies used. Distinguish a proved failing estimate, an unproved interface, a numerical diagnostic and a not-yet-completed review.

If possible provide a minimal derivation or executable countercheck. A finite mesh is diagnostic unless accompanied by rigorous control of the whole domain. A repair that changes the point family, derivative range, angular support or particle window must be identified as a scope change.

Audit and reproduction records are immutable historical evidence. Corrections should be separate dated addenda; they must not silently overwrite the original solver verdict or original hash. New mathematics requires review of its dependencies and cannot inherit a previous PASS label automatically.
