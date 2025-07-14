# Shearer's Theorem on Triangle-Free Graphs

A formal proof in Lean 4 of Shearer's theorem (shearer1983) on the lower bound on the independence number of triangle-free graphs in terms of their average degree.

## Main Statement

If $G$ is a triangle-free graph on $n$ vertices with average degree $d$, then its independence number $\alpha$ satisfies 

\[\alpha \geq n \cdot F(d),\] 

where 

\[F(x) = \begin{cases}
\frac{x \log x - x + 1}{(x - 1)^2} & \text{if } x \neq 1 \\
\frac{1}{2} & \text{if } x = 1
\end{cases}
\]

## Reference 
[J. B. Shearer, *A note on the independence number of triangle-free graphs*, Discrete Mathematics 46 (1983) 83-87] [shearer1983]