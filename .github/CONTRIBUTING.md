# Contributing to ephapax

This document explains how to contribute to the project. We follow a
"Dual-Track" architecture where human-readable documentation lives in
the root and machine-readable policies live in `.machine_readable/`.

## How to Contribute

We welcome contributions in many forms: \* **Code:** Improving the core
verified stack or extensions. \* **Documentation:** Enhancing AsciiDoc
manuals or AI manifests. \* **Testing:** Adding property-based tests or
formal proofs.

## Getting Started

1.  **Read the AI Manifest:** Start with `0-AI-MANIFEST.a2ml` to
    understand the repository structure.

2.  **Environment:** Use `guix` `develop` or `direnv` `allow` to set up
    your tools (Idris2, Zig, Rust).

3.  **Task Runner:** Use `just` to see available commands (`just`
    `--list`).

## Contribution Policies

For detailed rules on branch naming, commit messages, and the PR
process, please refer to the machine-readable metadata in
<a href="../.machine_readable/"
class="machine_readable/">.machine_readable/</a>.

## Code of Conduct

All contributors are expected to adhere to our ethical standards. See
<a href="CODE_OF_CONDUCT.md" class="md">CODE_OF_CONDUCT</a> for details.

## Signed commits

Every commit that reaches the default branch must be signed; a ruleset refuses
unsigned pushes. Estate policy:
[SIGNING-POLICY](https://github.com/hyperpolymath/standards/blob/main/docs/SIGNING-POLICY.adoc).

- **People and interactive agents** sign with an SSH key registered on GitHub
  as a *signing* key (`gpg.format=ssh`, `user.signingkey=<key>.pub`,
  `commit.gpgsign=true`). The committer email must be verified on that account.
- **Apps, bots and workflows** never `git push` local commits. They write
  through the API (`createCommitOnBranch` or the estate `signed-push` action)
  so that GitHub signs each commit.
- Merge PRs with **squash**. The ruleset checks every commit on the PR branch,
  not just the result, so one unsigned commit blocks the merge. Re-create such a
  branch with signed commits (`git cherry-pick -S`) and open a new PR.
  Rebase-merge replays commits unsigned and is disabled.
