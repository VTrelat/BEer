/* Principle: the partial function space X +-> Y is a predicate over option-valued
   functions, so functionality is built into the representation; membership of a
   maplet loosens that function to its graph. */
/* Check: declare-const ff \(-> Int \(Option Int\)\) */
/* Check: funGraph */
MACHINE M14PFun
SETS XX; YY
CONSTANTS ff, aa, bb, cc
PROPERTIES
  ff ∈ XX +-> YY ∧ aa ∈ XX ∧ bb ∈ YY ∧ cc ∈ YY ∧
  (aa ↦ bb) ∈ ff ∧ (aa ↦ cc) ∈ ff
ASSERTIONS
  bb = cc
END
