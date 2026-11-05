# drat-trim: comment on PR #43 (for Ahmet to post from his own GitHub account)

The bug was already reported. Issue #42 and PR #43 were both opened on 29 Sep 2026. The PR is the same one-line fix and is not merged yet. Opening a new issue would duplicate them, so a short comment on the PR is the better fit.

Where to post: https://github.com/marijnheule/drat-trim/pull/43

Text:

> We hit this in practice. We used `lrat-check` (master, last change 28c864a) to check more than 250,000 CaDiCaL LRAT proofs, streamed through a pipe, for a computer-assisted result in tournament Ramsey theory. An independent audit of our pipeline then showed that the final empty-clause step was never actually checked. So every "VERIFIED" verdict we had silently relied on the solver for that step. We reproduced it with the example from #42.
>
> We are now re-running all of the computations with exactly the change in this PR. In our tests it rejects the bogus proofs from #42 and accepts every genuine CaDiCaL proof we tried. Since others may rely on `lrat-check` the same way, it would be great to see this merged. Thank you for the tool.
