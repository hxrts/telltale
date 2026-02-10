# VM Contribution Checklist

All VM PRs should include this checklist in the PR body.

- [ ] I updated `docs/31_lean_rust_parity_matrix.md` for any changed parity surface.
- [ ] I included a parity impact statement describing whether behavior/encoding parity changed.
- [ ] I added or updated tests for changed observable VM behavior.
- [ ] If I introduced a parity break, I added a justified deviation entry in `docs/lean_vs_rust_deviations.json`.
- [ ] I included revisit date and owner for each active deviation.
