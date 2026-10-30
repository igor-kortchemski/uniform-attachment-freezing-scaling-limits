# Local formalization skills

Installed on 29 October 2026 from `lean-palomar-skills-updated`. The six skill
directories are unmodified copies, including UI metadata and references.
macOS `.DS_Store` files are excluded.

| Skill | Purpose |
| --- | --- |
| [lean-workflow](skills/lean-workflow/SKILL.md) | Everyday proof development |
| [lean-project-architecture](skills/lean-project-architecture/SKILL.md) | Mathematical encodings and module design |
| [lean-statement-audit](skills/lean-statement-audit/SKILL.md) | Statement fidelity, coverage, and proof review |
| [lean-elaboration](skills/lean-elaboration/SKILL.md) | Performance diagnosis |
| [lean-orchestrator](skills/lean-orchestrator/SKILL.md) | Coordination and integration |
| [lean-publication](skills/lean-publication/SKILL.md) | GitHub and Palomar preparation when requested |

Use `$lean-workflow` for ordinary proof work and load the other skills as needed.
For automatic local discovery, use `freezing2` as the Codex working directory;
the skills will be available on the next turn there. From the parent workspace,
read [AGENTS.md](../AGENTS.md) and load the linked skills directly. See the
[official OpenAI documentation](https://learn.chatgpt.com/docs/build-skills#where-codex-loads-local-skills).

The project's [formalization report](../FORMALIZATION_REPORT.md) and
[manuscript recommendations](../MANUSCRIPT_RECOMMENDATIONS.md) are initialized
for this paper. Original [report](templates/FORMALIZATION_REPORT.md) and
[recommendations](templates/MANUSCRIPT_RECOMMENDATIONS.md) templates are retained
for guidance.

[Attribution](skill-notices/lean-palomar-skills-updated/ATTRIBUTION.md),
the [CC BY 4.0 license](skill-notices/lean-palomar-skills-updated/LICENSE), and
the applicable third-party licenses remain together under
`skill-notices/lean-palomar-skills-updated/`. These notices cover the copied skill
material and templates. The project reports adapt those templates. This setup
does not assign a license to the manuscript or Lean code.
