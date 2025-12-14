# Balanced Vector Optimization - Lean 4 Blueprint

This repository contains a Lean 4 formalization of the following theorem:

> **Theorem.** Let $D : E(n,d) \to \mathbb{Q}$ be a function on weak compositions satisfying:
> 1. $S_n$-symmetry: $D(e \circ \sigma^{-1}) = D(e)$ for all permutations $\sigma$
> 2. Log-concavity: $D(e)^2 \geq D(e - \delta_i + \delta_j) \cdot D(e + \delta_i - \delta_j)$
> 3. Strict positivity: $D(e) > 0$
>
> Then:
> - **Maximum:** $D$ is maximized on *balanced* vectors ($|e_i - e_j| \leq 1$ for all $i,j$)
> - **Minimum:** $D$ is minimized on *concentrated* vectors ($e = d \cdot \delta_k$ for some $k$)

## Application

The main application is to descendant integrals on moduli spaces of curves:
$$\langle \tau_{e_1} \cdots \tau_{e_n} \rangle_g = \int_{\overline{\mathcal{M}}_{g,n}} \psi_1^{e_1} \cdots \psi_n^{e_n}$$

These satisfy the hypotheses via:
- Symmetry from the $S_n$ action permuting marked points
- Log-concavity from Khovanskii–Teissier inequalities (since $\psi$-classes are nef)
- Positivity from effectiveness of nef classes

## Blueprint

The blueprint website (with dependency graphs and proof status) is available at:
**[https://schmittj.github.io/balanced-vectors-blueprint/](https://schmittj.github.io/balanced-vectors-blueprint/)**

## Building

### Lean project
```bash
lake exe cache get   # Download mathlib cache
lake build           # Build the project
```

### Blueprint website
```bash
pip install leanblueprint
cd blueprint
leanblueprint all
# Output in blueprint/web/
```

## File Structure

- `BalancedVectors.lean` - Main Lean 4 formalization
- `blueprint/` - Blueprint documentation
  - `src/content.tex` - LaTeX source with Blueprint annotations
  - `blueprint.toml` - Blueprint configuration
- `.github/workflows/` - CI/CD for building and deploying

## Main Lean Definitions and Theorems

| Name | Type | Description |
|------|------|-------------|
| `WeakComposition n d` | Structure | n-tuple with sum d and non-negative entries |
| `IsBalanced` | Definition | All entries differ by at most 1 |
| `IsConcentrated` | Definition | All mass on one index |
| `SymmetricLogConcaveFunction` | Structure | Bundles D with its 3 properties |
| `main_theorem` | Theorem | Combined max/min result |

## License

This project is released under the Apache 2.0 license.

## Acknowledgments

This formalization accompanies the paper *"Extremal descendant integrals on moduli spaces of curves"* by Johannes Schmitt.
