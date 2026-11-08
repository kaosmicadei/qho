# Quantum Harmonic Oscillator
This repo is part of a journey of a physicist trying to learn Lean.

As a physicist’s "Hello, world" in Lean, this repo proves some properties of the [quantum harmonic oscillator](https://en.wikipedia.org/wiki/Quantum_harmonic_oscillator).

I’m not aiming for a complete formalisation since the focus is on learning how to prove statements in Lean rather than on fully formalising the quantum harmonic oscillator.

So, instead of using the usual analytical approach with differential equations, this repo focuses on the algebraic properties of the ladder operators, $`\boldsymbol{a}`$ and $`\boldsymbol{a}^\dagger`$, and the number operator $`\boldsymbol{N} = \boldsymbol{a}^\dagger \boldsymbol{a}`$.

Technically, it doesn't prove properties of the quantum harmonic oscillator itself, but rather properties of the number operator and its eigenvalues.

## Main results
The file `Qho.lean` uses the ladder operators $`\boldsymbol{a}`$ (annihilation) and $`\boldsymbol{a}^\dagger`$ (creation) as opaque $\mathbb{C}$-linear maps on a complex inner product space, satisfying:
- the canonical commutation relation $`[\boldsymbol{a}, \boldsymbol{a}^\dagger]=1`$, and 
- the adjoint relation $`\langle \boldsymbol{a} x, y\rangle = \langle x, \boldsymbol{a}^\dagger y\rangle`$.

The two main results proved in `Qho.lean` are:
- `eigenvalue_mem_nat`: If $`\boldsymbol{N} x = c \cdot x`$ for some $`x \neq 0`$, then $`c`$ is a natural number.
- `number_eq_nat_realized`: Given one non-zero eigenstate, for every $`n:\mathbb{N}`$ there is a non-zero state $`y`$ such that $`\boldsymbol{N} y = n \cdot y`$.

## Limitations
Since the result here is algebraic, there are two important limitations:
1. The operators are arbitrary endomorphisms satisfying the canonical commutation relation and adjoint hypotheses. The concrete $`\boldsymbol{a} = \sqrt{(m\omega/2\hbar)}(\boldsymbol{x} + i\boldsymbol{p}/m\omega)`$ on $`L^2(\mathbb{R})`$ is not constructed.
2. Results are conditional on the existence of eigenstates. Existence of the ground state from scratch, completeness of the eigenstates, and the unbounded-operator nature of $`a`$ and $`a^\dagger`$ are out of scope.

## Notes
This was a learning exercise, so the proofs aim for explicitness rather than brevity. Many optimisations and simplifications could be made, but the focus here was on understanding how to use Lean for algebraic manipulations in quantum mechanics.