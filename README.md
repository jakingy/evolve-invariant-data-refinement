# Isabelle theory contributions

This repository is a source snapshot of James King's contributions to
`isabelle/new_rg_algebra/` at `dv4cs` commit `e0ce56461dcce28073e178b87fd5120e0c95ce14`. Complete theories are in
`theories/`. For theories that already existed, `excerpts/` contains only
the selected declarations, their adjacent preceding text, and their full
proof bodies. Excerpt files preserve Isabelle source but are not standalone
buildable theories. The parent repository supplies their context and imports.

Selection uses Git blame: a declaration is included when its statement,
proof, or adjacent preceding text has lines attributed to James King.
This does not imply sole authorship of every line in an excerpt. The
snapshot includes current working-tree edits within the selected source.
`manifest.json` records original paths and declaration lines.

The `DEAD/` theories are archived and are not part of the current Isabelle
sessions. Rename history is followed when distinguishing new theories
from extensions to pre-existing theories, including `GhostAssignments.thy`.

Thesis links use a specific commit and `#L` line anchors. They continue
to identify that source snapshot when the default branch is updated.

| Original theory | Export | Declarations |
| --- | --- | ---: |
| `Atomic/Distributive_Laws.thy` | [selected source excerpts](excerpts/Atomic/Distributive_Laws.thy) | 12 |
| `Biquantale/Biquantale_Assert.thy` | [selected source excerpts](excerpts/Biquantale/Biquantale_Assert.thy) | 2 |
| `Biquantale/Biquantale_Precondition.thy` | [selected source excerpts](excerpts/Biquantale/Biquantale_Precondition.thy) | 1 |
| `Commands/Assignments.thy` | [selected source excerpts](excerpts/Commands/Assignments.thy) | 8 |
| `Commands/Bind.thy` | [complete theory](theories/Commands/Bind.thy) | 13 |
| `Commands/Data_Refinement.thy` | [selected source excerpts](excerpts/Commands/Data_Refinement.thy) | 58 |
| `Commands/Expressions.thy` | [selected source excerpts](excerpts/Commands/Expressions.thy) | 8 |
| `Commands/Expressions_Mref.thy` | [selected source excerpts](excerpts/Commands/Expressions_Mref.thy) | 21 |
| `DEAD/Bind.thy` | [complete theory](theories/DEAD/Bind.thy) | 66 |
| `DEAD/GhostAssignments.thy` | [complete theory](theories/DEAD/GhostAssignments.thy) | 6 |
| `Examples/Circular_Buffer.thy` | [complete theory](theories/Examples/Circular_Buffer.thy) | 49 |
| `Examples/Queue.thy` | [complete theory](theories/Examples/Queue.thy) | 11 |
| `Examples/Remove.thy` | [complete theory](theories/Examples/Remove.thy) | 12 |
| `Examples/Remove_Array.thy` | [complete theory](theories/Examples/Remove_Array.thy) | 34 |
| `Examples/Typed_State.thy` | [complete theory](theories/Examples/Typed_State.thy) | 18 |
| `Quantale/Quantale.thy` | [selected source excerpts](excerpts/Quantale/Quantale.thy) | 1 |
| `Quantale/Quantale_Assert.thy` | [selected source excerpts](excerpts/Quantale/Quantale_Assert.thy) | 2 |
| `Quantale/Quantale_Test.thy` | [selected source excerpts](excerpts/Quantale/Quantale_Test.thy) | 3 |
| `Rely_Guarantee/Atomic_Specification.thy` | [selected source excerpts](excerpts/Rely_Guarantee/Atomic_Specification.thy) | 43 |
| `Rely_Guarantee/Evolve.thy` | [complete theory](theories/Rely_Guarantee/Evolve.thy) | 26 |
| `Rely_Guarantee/Frame.thy` | [selected source excerpts](excerpts/Rely_Guarantee/Frame.thy) | 4 |
| `Rely_Guarantee/Guarantee.thy` | [selected source excerpts](excerpts/Rely_Guarantee/Guarantee.thy) | 3 |
| `Rely_Guarantee/Invariant.thy` | [complete theory](theories/Rely_Guarantee/Invariant.thy) | 60 |
| `Rely_Guarantee/Optional_Command.thy` | [selected source excerpts](excerpts/Rely_Guarantee/Optional_Command.thy) | 6 |
| `Rely_Guarantee/Rely.thy` | [selected source excerpts](excerpts/Rely_Guarantee/Rely.thy) | 9 |
| `Rely_Guarantee/Rely_Guarantee.thy` | [selected source excerpts](excerpts/Rely_Guarantee/Rely_Guarantee.thy) | 14 |
| `Rely_Guarantee/State_Relations.thy` | [selected source excerpts](excerpts/Rely_Guarantee/State_Relations.thy) | 29 |
| `Rely_Guarantee/Termination.thy` | [selected source excerpts](excerpts/Rely_Guarantee/Termination.thy) | 6 |
