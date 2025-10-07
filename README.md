# Bounds for Triangle-Free Graphs

A Lean 4 formalisation of two bounds for triangle-free graphs:
the classical lower bound on the independence number due to Shearer
[Shearer1983], and our recent lower bound on the total number of independent
sets from [BvdHK2025].

## Main Statements

The two main statements can be found in the file `ShearerTriangleFreeInd/Main.lean`.

- **Independence number.**  
  If $G$ is a triangle-free graph on $n$ vertices with average degree $d$, then
  its independence number $\alpha$ satisfies

  $$\alpha \geq n \cdot F(d)$$

  where

  $$
  F(x) =
  \begin{cases}
    \tfrac12, & x = 1,\\[0.4em]
    \dfrac{x \log x - x + 1}{(x - 1)^2}, & x \neq 1.
  \end{cases}
  $$

- **Independent set count.**  
  If $G$ is a triangle-free graph on $n$ vertices with average degree $d$, then
  the number of independent sets satisfies

  $$
  \lvert \mathcal{I}(G) \rvert \geq \exp\bigl(n \cdot G(d)\bigr),
  $$

  where $W$ is the principal branch of the Lambert $W$ function and

  $$
  G(x) =
  \begin{cases}
    e^{-W(2)}, & x = 2,\\[0.4em]
    \dfrac{\tfrac12 W(x)^2 + W(x) - \bigl(\tfrac12 W(2)^2 + W(2)\bigr)}{x - 2},
      & x \neq 2.
  \end{cases}
  $$

## Project Structure

- `ShearerTriangleFreeInd/Analysis.lean` – Properties of the Shearer function
  `F`, including convexity and auxiliary calculus lemmas.
- `ShearerTriangleFreeInd/Analysis_W.lean` – Construction and analysis of the
  Lambert $W$ function needed for the counting bound, and analysis of the above function 
  `G`.
- `ShearerTriangleFreeInd/Proofs.lean` – Core combinatorial lemmas and the
  proofs of both bounds.
- `ShearerTriangleFreeInd/Main.lean` – Contains only the two main statements.

## References
- [Shearer1983] J. B. Shearer, *A note on the independence number of
  triangle-free graphs*, Discrete Mathematics 46 (1983), 83–87.
- [BvdHK2025] Pjotr Buys, Jan van den Heuvel, Ross J. Kang, *Triangle-free graphs with the fewest independent sets*, [arXiv:2503.10002](https://arxiv.org/pdf/2503.10002) (2025).